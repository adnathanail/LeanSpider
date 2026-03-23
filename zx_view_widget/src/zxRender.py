import json
from fractions import Fraction

from pyzx.drawing import graph_json
from pyzx.graph import Graph
from pyzx.graph.base import BaseGraph
from pyzx.utils import EdgeType, VertexType, settings

type ZXLeanGraph = BaseGraph[int, int]


def leanzx_to_pyzx(data) -> ZXLeanGraph:
    """Convert LeanZX JSON to a pyzx Graph."""
    g: ZXLeanGraph = Graph()
    nodes = data.get("nodes", [])
    edges = data.get("edges", [])

    inputs: list[int] = []
    outputs: list[int] = []

    for node in nodes:
        nid = node["id"]
        ntype = node["type"]

        # Manually adding vertex and setting type/row/qubit so that we can set
        #   the vertex indices manually, so that they align with the node IDs
        #   in PyZX
        # Essentially unrolling the g.add_vertex function
        g.add_vertex_indexed(nid)

        if ntype == "input":
            g.set_type(nid, VertexType.BOUNDARY)
            g.set_row(nid, 0)
            g.set_qubit(nid, node.get("ioId", 0))
            inputs.append(nid)
        elif ntype == "output":
            g.set_type(nid, VertexType.BOUNDARY)
            g.set_row(nid, -1)
            g.set_qubit(nid, node.get("ioId", 0))
            outputs.append(nid)
        elif ntype == "spider":
            color = node.get("color", "Z")
            ty = VertexType.Z if color == "Z" else VertexType.X
            phase_str = node.get("phase", "0")
            phase = _parse_phase(phase_str)
            g.set_type(nid, ty)
            g.set_phase(nid, phase)
        elif ntype == "hadamard":
            phase_str = node.get("phase", "0")
            phase = _parse_phase(phase_str)
            g.set_type(nid, VertexType.H_BOX)
            g.set_phase(nid, phase)
        else:
            g.set_type(nid, VertexType.BOUNDARY)

    for edge in edges:
        g.add_edge((edge["src"], edge["tgt"]), edgetype=EdgeType.SIMPLE)

    g.set_inputs(tuple(inputs))
    g.set_outputs(tuple(outputs))

    # Auto-layout spider positions
    _auto_layout(g)

    return g


def _parse_phase(s):
    """Parse a phase string like '0', '1', '1/2' into a Fraction."""
    s = s.strip()
    if "/" in s:
        return Fraction(s)
    return Fraction(int(s))


def _auto_layout(g: ZXLeanGraph):
    """Simple left-to-right layout based on graph distance from inputs."""
    inputs = g.inputs()
    outputs = g.outputs()
    if not inputs:
        return

    # BFS from inputs to assign rows to interior vertices
    visited = {}
    queue = list(inputs)
    for v in queue:
        visited[v] = 0

    while queue:
        current = queue.pop(0)
        for neighbor in g.neighbors(current):
            if neighbor not in visited:
                visited[neighbor] = visited[current] + 1
                queue.append(neighbor)

    # Set rows for non-boundary vertices
    max_depth = max(visited.values(), default=1)
    for v, depth in visited.items():
        if v not in inputs and v not in outputs:
            g.set_row(v, depth)

    # Set output row to max_depth
    for v in outputs:
        g.set_row(v, max_depth)

    # Assign qubit indices to interior vertices, avoiding collisions
    # First, record which qubit slots are already taken per row (by inputs/outputs)
    row_taken: dict[int, set[int]] = {}
    for v in inputs:
        r = int(g.row(v))
        row_taken.setdefault(r, set()).add(int(g.qubit(v)))
    for v in outputs:
        r = int(g.row(v))
        row_taken.setdefault(r, set()).add(int(g.qubit(v)))

    row_counts: dict[int, int] = {}
    for v in g.vertices():
        if v in inputs or v in outputs:
            continue
        r = int(g.row(v))
        count = row_counts.get(r, 0)
        taken = row_taken.get(r, set())
        # Skip slots occupied by boundary nodes
        while count in taken:
            count += 1
        g.set_qubit(v, count)
        row_counts[r] = count + 1


def render(diagram_json: str) -> str:
    """Convert a ZXDiagram JSON string to pyzx's D3-compatible graph JSON.

    Returns a JSON string with {nodes, links} ready for the D3 viewer,
    plus width/height/scale/node_size for rendering.
    """
    data = json.loads(diagram_json)
    g = leanzx_to_pyzx(data)

    # Compute scale and dimensions (same logic as pyzx's draw_d3)
    minrow = min((g.row(v) for v in g.vertices()), default=0)
    maxrow = max((g.row(v) for v in g.vertices()), default=0)
    minqub = min((g.qubit(v) for v in g.vertices()), default=0)
    maxqub = max((g.qubit(v) for v in g.vertices()), default=0)

    scale = 800 / (maxrow - minrow + 2)
    if scale > 50:
        scale = 50
    if scale < 20:
        scale = 20

    w = (maxrow - minrow + 2) * scale
    h = (maxqub - minqub + 3) * scale
    node_size = max(0.2 * scale, 2)

    coords = {v: ((g.row(v) - minrow + 1) * scale, (g.qubit(v) - minqub + 2) * scale, 0) for v in g.vertices()}

    graph_j = graph_json(g, coords)

    return json.dumps(
        {
            "graph": json.loads(graph_j),
            "width": w,
            "height": h,
            "scale": scale,
            "node_size": node_size,
            "colors": settings.colors,
        }
    )
