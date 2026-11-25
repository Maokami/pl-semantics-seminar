import PLBook

open Verso Verso.Genre Verso.Genre.Manual
open Verso.Output.Html

def main := manualMain (%doc PLBook) (config := {
  htmlDepth := 1
  emitHtmlMulti := .immediately
  extraFiles := [("static", "static")]
  extraHead := #[
    {{<link rel="stylesheet" href="static/reader.css"/>}},
    {{<script defer="defer" src="static/reader.js"></script>}}]
})
