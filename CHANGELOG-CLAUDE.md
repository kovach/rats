# 26/02/12
automatic port derp implementation to rust:

  - 13b6110 [CLAUDE,UNREVIEWED] used claude to mostly automatically port Derp to rust. performance is still not significantly better; need to improve ownership structure
  - see [plan](rust-derp/PLAN.md)
  - some remaining issues:
    - [scott] review
    - parser should use combinators
    - too much copying
  - anecdotes:
    - after the first pass on the code, claude tried to generate a derp program for testing.
      its output had a minor error (wrote `foo a.` instead of `-- foo a.`, like traditional syntax),
      failed to parse, it read the parse error (from the parser it had just implemented) and fixed.

# 26/02/11
used claude code to make starter code for a webserver, generate a simple html view, and make a new module:

  - 938fb86 Move Derp modules into Derp/ subpackage, split types from core
  - 4c5a5b6 Serialize Tuples to JSON, serve HTML view over WebSocket
  - b8412a6 Add web server with warp + wai-websockets + aeson
