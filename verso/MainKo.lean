import PLBook.Korean

open Verso Verso.Genre Verso.Genre.Manual Verso.Output.Html

def main := manualMain (%doc PLBook.Korean)
  (config := {
    htmlDepth := 1
    emitHtmlMulti := .immediately
    extraHead := #[
      {{<link rel="stylesheet" href="static/reader.css"/>}},
      {{<script defer="defer" src="static/reader.js"></script>}}]
  })
