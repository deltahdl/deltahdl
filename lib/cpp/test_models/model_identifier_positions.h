#pragma once

#include <algorithm>
#include <initializer_list>
#include <string>
#include <string_view>

// The identifier positions a word can be put in, each reached by its own
// grammar production. A reserved-word sweep puts a word into a position and
// checks that the source is accepted or rejected, so the positions are the
// sweep's coverage: a declaration's own name slot is only one of them, and a
// word that stopped being reserved in just one of the others would go
// unnoticed by a sweep that used the declaration slot alone.

// One position. `what` names the production for a failure message, and `tmpl`
// is a source with '@' standing wherever the word under test goes.
struct IdentifierPosition {
  const char* what;
  const char* tmpl;
};

inline constexpr IdentifierPosition kIdentifierPositions[] = {
    {"design element", "module @;\nendmodule\n"},
    {"port",
     "module m (input wire @, output wire y);\n"
     "  assign y = @;\n"
     "endmodule\n"},
    {"instance",
     "module ch (input wire a, output wire y);\n"
     "  assign y = a;\n"
     "endmodule\n"
     "module top;\n"
     "  wire a, b;\n"
     "  ch @ (.a(a), .y(b));\n"
     "endmodule\n"},
    {"task",
     "module m;\n"
     "  reg [7:0] r;\n"
     "  task @; r = 8'd1; endtask\n"
     "  initial begin : blk @; end\n"
     "endmodule\n"},
    {"function",
     "module m;\n"
     "  reg [7:0] r;\n"
     "  function [7:0] @(input reg [7:0] n);\n"
     "    @ = n + n;\n"
     "  endfunction\n"
     "  initial r = @(8'd4);\n"
     "endmodule\n"},
    {"gate instance",
     "module m (input wire a, output wire y);\n"
     "  and @ (y, a, a);\n"
     "endmodule\n"},
    {"genvar",
     "module m;\n"
     "  genvar @;\n"
     "  generate\n"
     "    for (@ = 0; @ < 2; @ = @ + 1) begin : blk\n"
     "      reg [7:0] slot;\n"
     "    end\n"
     "  endgenerate\n"
     "endmodule\n"},
    {"named block",
     "module m;\n"
     "  reg [7:0] r;\n"
     "  initial begin : @ r = 8'd1; end\n"
     "endmodule\n"},
};

// Substitutes `word` for every placeholder in one position's template.
inline std::string AtPosition(const IdentifierPosition& p, const char* word) {
  std::string src = p.tmpl;
  for (auto at = src.find('@'); at != std::string::npos;
       at = src.find('@', at + 1)) {
    src.replace(at, 1, word);
  }
  return src;
}

// Whether `p` is one of the positions `what` names, for a sweep that covers
// some of them rather than all -- either because the rest are carried by
// another sweep, or because a word cannot be driven through them.
inline bool PositionIsOneOf(const IdentifierPosition& p,
                            std::initializer_list<std::string_view> what) {
  return std::find(what.begin(), what.end(), std::string_view(p.what)) !=
         what.end();
}
