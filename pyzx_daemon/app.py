import base64
import io
from fractions import Fraction

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

import pyzx as zx
from pyzx.utils import VertexType, EdgeType
from flask import Flask, request, jsonify
from flask_cors import CORS

app = Flask(__name__)
CORS(app)


def zxlean_to_pyzx(data):
    """Convert ZxLean JSON to a pyzx Graph."""
    g = zx.Graph()
    nodes = data.get("nodes", [])
    edges = data.get("edges", [])

    # Map from ZxLean node id -> pyzx vertex id
    id_map = {}
    inputs = []
    outputs = []

    for node in nodes:
        nid = node["id"]
        ntype = node["type"]

        if ntype == "input":
            v = g.add_vertex(ty=VertexType.BOUNDARY, row=0, qubit=node.get("ioId", 0))
            inputs.append(v)
        elif ntype == "output":
            v = g.add_vertex(ty=VertexType.BOUNDARY, row=-1, qubit=node.get("ioId", 0))
            outputs.append(v)
        elif ntype == "spider":
            color = node.get("color", "Z")
            ty = VertexType.Z if color == "Z" else VertexType.X
            phase_str = node.get("phase", "0")
            phase = _parse_phase(phase_str)
            v = g.add_vertex(ty=ty, phase=phase)
        else:
            v = g.add_vertex(ty=VertexType.BOUNDARY)

        id_map[nid] = v

    for edge in edges:
        src = id_map[edge["src"]]
        tgt = id_map[edge["tgt"]]
        g.add_edge((src, tgt), edgetype=EdgeType.SIMPLE)

    # Set outputs to max row + 1
    max_row = max((g.row(v) for v in g.vertices() if g.row(v) >= 0), default=0)
    for v in outputs:
        g.set_row(v, max_row + 1)

    g.set_inputs(inputs)
    g.set_outputs(outputs)

    # Auto-layout spider positions
    _auto_layout(g)

    return g


def _parse_phase(s):
    """Parse a phase string like '0', '1', '1/2' into a Fraction."""
    s = s.strip()
    if "/" in s:
        return Fraction(s)
    return Fraction(int(s))


def _auto_layout(g):
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


def render_to_base64(g):
    """Render a pyzx graph to a base64-encoded PNG string."""
    fig = zx.draw_matplotlib(g, labels=True, figsize=(8, 2))
    buf = io.BytesIO()
    fig.savefig(buf, format="png", bbox_inches="tight", dpi=150)
    plt.close(fig)
    buf.seek(0)
    return base64.b64encode(buf.read()).decode("ascii")


@app.route("/diagram", methods=["POST"])
def diagram():
    data = request.get_json()
    try:
        g = zxlean_to_pyzx(data)
        image = render_to_base64(g)
        return jsonify({"status": "ok", "image": image})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500


if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5050)
