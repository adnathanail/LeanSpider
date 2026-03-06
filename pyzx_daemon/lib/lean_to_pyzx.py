from fractions import Fraction

from pyzx.graph import Graph
from pyzx.utils import EdgeType, VertexType

from .types import ZXLeanGraph


def zxlean_to_pyzx(data) -> ZXLeanGraph:
    """Convert ZxLean JSON to a pyzx Graph."""
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
        else:
            g.set_type(nid, VertexType.BOUNDARY)

    for edge in edges:
        g.add_edge((edge["src"], edge["tgt"]), edgetype=EdgeType.SIMPLE)

    # Set outputs to max row + 1
    max_row = max((g.row(v) for v in g.vertices() if g.row(v) >= 0), default=0)
    for v in outputs:
        g.set_row(v, max_row + 1)

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

    # Assign qubit indices to interior vertices that don't have one
    row_counts = {}
    for v in g.vertices():
        if v in inputs or v in outputs:
            continue
        r = g.row(v)
        count = row_counts.get(r, 0)
        g.set_qubit(v, count)
        row_counts[r] = count + 1
