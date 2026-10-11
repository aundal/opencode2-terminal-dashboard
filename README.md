# opencode2-terminal-dashboard

An [OpenCode](https://opencode.ai) **V2** plugin that serves a live web dashboard and draws
every open session as a figure standing on an isometric floor.

The floor is split into **four equal quarters**, one per status class. A figure never leaves
the quarter its status puts it in.

| Zone  | Status                                          | Screen corner |
| ----- | ----------------------------------------------- | ------------- |
| Green | `running`, `compacting`                         | far           |
| Orange| `user_response`, `asking_parent`                | left          |
| Red   | `failed`, `retrying`, `interrupted`             | near          |
| Grey  | everything else, including `idle` and `closed`  | right         |

`interrupted` is red, not grey. It is stuck, not idle.

## Features

- **One room for every session** - grouping (directory, label, status) decides the shirt
  colour, so you can see which project someone belongs to without splitting the office up
- **Real statuses** - the server is authoritative for status, title and cost; the heartbeat
  only enriches
- **Figures that work** - a working figure types, a failed one throws its arms about to get
  attention, a blocked one waits with its hands still
- **Isometric, not stacked** - proper 2:1 projection with painter's-algorithm depth sorting,
  so a figure walks *behind* what is in front of it
- **Named states, visible** - every figure carries its current state as a label
- **A* pathfinding** - figures move between three stable points inside their own quarter
- **Pan and zoom** - scroll to zoom, right-click drag to move, double-click to reset
- **Debug panel** - `Ctrl+D` or the `Debug` button, then click a figure for its state,
  timeline and time remaining
- **Three views** - compact, standard and extended

## Install

Register the package in `opencode.json`:

```json
{ "plugins": ["opencode2-terminal-dashboard"] }
```

The plugin starts a local HTTP server and prints the URL when the CLI comes up.

## Configuration

| Variable           | Default | Meaning                                                    |
| ------------------ | ------- | ---------------------------------------------------------- |
| `DASHBOARD_PORT`   | `31337` | Port the dashboard listens on                               |
| `DASHBOARD_TOKEN`  | _unset_ | If set, required on the read endpoints                      |

### A note on `DASHBOARD_TOKEN`

The dashboard binds to `0.0.0.0`, so it is reachable from every interface on the machine.
If `DASHBOARD_TOKEN` is unset, the write and heartbeat endpoints accept unauthenticated
requests. On a single-user machine that is fine; if anything else on your network can reach
port 31337, set the variable.

The dashboard password itself is never stored in this repo. It is read at runtime from
`~/.local/state/opencode/service.json`.

## Views

Switch view in the settings menu: **Compact**, **Normal** and **Extended**.

The isometric office is a fourth view (`house`). It has no button in the settings menu. To
turn it on, run this once in the dashboard console:

```js
localStorage.setItem('dashboardInfoMode', 'house'); location.reload()
```

Set it back to `'standard'` to return to the card list.

## License

MIT - see [LICENSE](LICENSE).