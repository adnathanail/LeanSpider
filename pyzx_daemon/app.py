from flask import Flask, jsonify, request
from flask_cors import CORS

from lib.lean_to_pyzx import leanzx_to_pyzx
from lib.pyzx_to_img import render_to_base64

app = Flask(__name__)
CORS(app)


@app.route("/diagram", methods=["POST"])
def diagram():
    data = request.get_json()
    try:
        g = leanzx_to_pyzx(data)
        image = render_to_base64(g)
        return jsonify({"status": "ok", "image": image})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--host", required=True)
    parser.add_argument("--port", type=int, required=True)
    parser.add_argument("--debug", action="store_true")
    args = parser.parse_args()

    app.run(host=args.host, port=args.port, debug=args.debug)
