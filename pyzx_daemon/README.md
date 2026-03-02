The daemon starts automatically when `ZxLean.Visualize` is imported

Logs are written to `pyzx_daemon.log`

To start it manually:

```sh
uv sync
uv run python app.py
```

The server runs on `http://127.0.0.1:5050`. You can test it with:

```sh
curl -X POST http://127.0.0.1:5050/diagram \
  -H "Content-Type: application/json" \
  -d '{"nodes":[],"edges":[]}'
```