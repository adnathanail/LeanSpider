import base64
import io
import json
from fractions import Fraction

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import pyzx as zx
from pyzx.utils import EdgeType, VertexType


def _parse_phase(s):
    s = s.strip()
    if '/' in s:
        return Fraction(s)
    return Fraction(int(s))


def _auto_layout(g):
    inputs = g.inputs()
    outputs = g.outputs()
    if not inputs:
        return

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

    max_depth = max(visited.values(), default=1)
    for v, depth in visited.items():
        if v not in inputs and v not in outputs:
            g.set_row(v, depth)

    for v in outputs:
        g.set_row(v, max_depth)

    row_taken = {}
    for v in inputs:
        r = int(g.row(v))
        row_taken.setdefault(r, set()).add(int(g.qubit(v)))
    for v in outputs:
        r = int(g.row(v))
        row_taken.setdefault(r, set()).add(int(g.qubit(v)))

    row_counts = {}
    for v in g.vertices():
        if v in inputs or v in outputs:
            continue
        r = int(g.row(v))
        count = row_counts.get(r, 0)
        taken = row_taken.get(r, set())
        while count in taken:
            count += 1
        g.set_qubit(v, count)
        row_counts[r] = count + 1


def render(diagram_json: str) -> str:
    """Convert a ZXDiagram JSON string to a base64-encoded PNG via pyzx."""
    data = json.loads(diagram_json)
    g = zx.Graph()

    inputs = []
    outputs = []

    for node in data['nodes']:
        nid = node['id']
        ntype = node['type']

        g.add_vertex_indexed(nid)

        if ntype == 'input':
            g.set_type(nid, VertexType.BOUNDARY)
            g.set_row(nid, 0)
            g.set_qubit(nid, node.get('ioId', 0))
            inputs.append(nid)
        elif ntype == 'output':
            g.set_type(nid, VertexType.BOUNDARY)
            g.set_row(nid, -1)
            g.set_qubit(nid, node.get('ioId', 0))
            outputs.append(nid)
        elif ntype == 'spider':
            ty = VertexType.Z if node.get('color', 'Z') == 'Z' else VertexType.X
            g.set_type(nid, ty)
            g.set_phase(nid, _parse_phase(node.get('phase', '0')))
        elif ntype == 'hadamard':
            g.set_type(nid, VertexType.H_BOX)
            g.set_phase(nid, _parse_phase(node.get('phase', '0')))
        else:
            g.set_type(nid, VertexType.BOUNDARY)

    for edge in data['edges']:
        g.add_edge((edge['src'], edge['tgt']), edgetype=EdgeType.SIMPLE)

    max_row = max((g.row(v) for v in g.vertices() if g.row(v) >= 0), default=0)
    for v in outputs:
        g.set_row(v, max_row + 1)

    g.set_inputs(tuple(inputs))
    g.set_outputs(tuple(outputs))
    _auto_layout(g)

    rows = set(g.row(v) for v in g.vertices())
    qubits = set(g.qubit(v) for v in g.vertices())
    width = max(len(rows) * 1.5, 6)
    height = max(len(qubits) * 1.2, 2)

    fig = zx.draw_matplotlib(g, labels=True, figsize=(width, height))
    buf = io.BytesIO()
    fig.savefig(buf, format='png', bbox_inches='tight', dpi=150)
    plt.close(fig)
    buf.seek(0)
    return base64.b64encode(buf.read()).decode('ascii')
