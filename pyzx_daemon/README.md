The daemon starts automatically when `LeanZX.Visualize` is imported

Logs are written to `pyzx_daemon.log`

To start it manually:

```sh
uv sync
uv run python app.py --host 127.0.0.1 --port 5050 --debug
```

`--host` and `--port` are required flags (no defaults). The canonical values are defined in `LeanZX/Visualize.lean`.

The server runs on `http://127.0.0.1:5050`. You can test it with:

```sh
curl -X POST http://127.0.0.1:5050/diagram \
  -H "Content-Type: application/json" \
  -d '{"nodes":[],"edges":[]}'
```