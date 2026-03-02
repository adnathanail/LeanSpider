# ZxLean

## Widget development

The InfoView widget lives in `widget/src/`. After editing the TypeScript source:

```sh
cd widget
npm install   # first time only
npm run build # compiles TS, bundles JS, and invalidates Lean cache
cd ..
lake build    # picks up the new widget JS
```

## Python server

The widget sends diagram data to a local Flask server for processing. To start it:

```sh
cd pyzx_daemon
uv sync
uv run python app.py
```

The server runs on `http://127.0.0.1:5050`. You can test it with:

```sh
curl -X POST http://127.0.0.1:5050/diagram \
  -H "Content-Type: application/json" \
  -d '{"nodes":[],"edges":[]}'
```