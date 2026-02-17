# 26/02/16
## specialize rules once at startup
  - af752c6f74ae
  - see [plan](plans/4.md)
  - This was a more substantial change with very little prompting required.
    Its initial approach was incorrect, but it corrected it only being told a test failed.

# 26/02/14
## use serde
  - see [plan](plans/3.md)

# 26/02/12
## server
  - 9d0e7fa96
  - watch input files, compose hs/rs operations, better rendering.

## fix allocations
  - see [plan](plans/2.md)
  - also switched to mutable binding usage pattern

## automatic port derp implementation to rust:
  - 13b6110 [CLAUDE,UNREVIEWED] used claude to mostly automatically port Derp to rust. performance is still not significantly better; need to improve ownership structure
  - see [plan](plans/1.md)
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
