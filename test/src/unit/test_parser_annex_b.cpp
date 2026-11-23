#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <iterator>
#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

constexpr const char* kReservedKeywords[] = {
    "accept_on",
    "alias",
    "always",
    "always_comb",
    "always_ff",
    "always_latch",
    "and",
    "assert",
    "assign",
    "assume",
    "automatic",
    "before",
    "begin",
    "bind",
    "bins",
    "binsof",
    "bit",
    "break",
    "buf",
    "bufif0",
    "bufif1",
    "byte",
    "case",
    "casex",
    "casez",
    "cell",
    "chandle",
    "checker",
    "class",
    "clocking",
    "cmos",
    "config",
    "const",
    "constraint",
    "context",
    "continue",
    "cover",
    "covergroup",
    "coverpoint",
    "cross",
    "deassign",
    "default",
    "defparam",
    "design",
    "disable",
    "dist",
    "do",
    "edge",
    "else",
    "end",
    "endcase",
    "endchecker",
    "endclass",
    "endclocking",
    "endconfig",
    "endfunction",
    "endgenerate",
    "endgroup",
    "endinterface",
    "endmodule",
    "endpackage",
    "endprimitive",
    "endprogram",
    "endproperty",
    "endsequence",
    "endspecify",
    "endtable",
    "endtask",
    "enum",
    "event",
    "eventually",
    "expect",
    "export",
    "extends",
    "extern",
    "final",
    "first_match",
    "for",
    "force",
    "foreach",
    "forever",
    "fork",
    "forkjoin",
    "function",
    "generate",
    "genvar",
    "global",
    "highz0",
    "highz1",
    "if",
    "iff",
    "ifnone",
    "ignore_bins",
    "illegal_bins",
    "implements",
    "implies",
    "import",
    "incdir",
    "include",
    "initial",
    "inout",
    "input",
    "inside",
    "instance",
    "int",
    "integer",
    "interconnect",
    "interface",
    "intersect",
    "join",
    "join_any",
    "join_none",
    "large",
    "let",
    "liblist",
    "library",
    "local",
    "localparam",
    "logic",
    "longint",
    "macromodule",
    "matches",
    "medium",
    "modport",
    "module",
    "nand",
    "negedge",
    "nettype",
    "new",
    "nexttime",
    "nmos",
    "nor",
    "noshowcancelled",
    "not",
    "notif0",
    "notif1",
    "null",
    "or",
    "output",
    "package",
    "packed",
    "parameter",
    "pmos",
    "posedge",
    "primitive",
    "priority",
    "program",
    "property",
    "protected",
    "pull0",
    "pull1",
    "pulldown",
    "pullup",
    "pulsestyle_ondetect",
    "pulsestyle_onevent",
    "pure",
    "rand",
    "randc",
    "randcase",
    "randsequence",
    "rcmos",
    "real",
    "realtime",
    "ref",
    "reg",
    "reject_on",
    "release",
    "repeat",
    "restrict",
    "return",
    "rnmos",
    "rpmos",
    "rtran",
    "rtranif0",
    "rtranif1",
    "s_always",
    "s_eventually",
    "s_nexttime",
    "s_until",
    "s_until_with",
    "scalared",
    "sequence",
    "shortint",
    "shortreal",
    "showcancelled",
    "signed",
    "small",
    "soft",
    "solve",
    "specify",
    "specparam",
    "static",
    "string",
    "strong",
    "strong0",
    "strong1",
    "struct",
    "super",
    "supply0",
    "supply1",
    "sync_accept_on",
    "sync_reject_on",
    "table",
    "tagged",
    "task",
    "this",
    "throughout",
    "time",
    "timeprecision",
    "timeunit",
    "tran",
    "tranif0",
    "tranif1",
    "tri",
    "tri0",
    "tri1",
    "triand",
    "trior",
    "trireg",
    "type",
    "typedef",
    "union",
    "unique",
    "unique0",
    "unsigned",
    "until",
    "until_with",
    "untyped",
    "use",
    "uwire",
    "var",
    "vectored",
    "virtual",
    "void",
    "wait",
    "wait_order",
    "wand",
    "weak",
    "weak0",
    "weak1",
    "while",
    "wildcard",
    "wire",
    "with",
    "within",
    "wor",
    "xnor",
    "xor",
};

constexpr size_t kReservedKeywordCount = std::size(kReservedKeywords);

std::string VarDecl(std::string_view word) {
  return "module m;\n  reg [7:0] " + std::string(word) + ";\nendmodule\n";
}

bool IsConstructorWord(std::string_view word) { return word == "new"; }

bool HasOperandRoleOfItsOwn(std::string_view word) {
  constexpr std::string_view kWithOperandRole[] = {
      "bit",      "byte",      "const",  "int",    "integer",  "logic",
      "longint",  "new",       "null",   "real",   "realtime", "reg",
      "shortint", "shortreal", "signed", "string", "super",    "this",
      "time",     "unsigned",  "void",
  };
  for (std::string_view candidate : kWithOperandRole) {
    if (candidate == word) return true;
  }
  return false;
}

struct Position {
  const char* what;
  const char* tmpl;
  bool (*excluded)(std::string_view);
  size_t expected_swept;
};
constexpr Position kPositions[] = {
    {"design element", "module @;\nendmodule\n", nullptr, 248},
    {"port",
     "module m (input wire @, output wire y);\n"
     "  assign y = @;\n"
     "endmodule\n",
     nullptr, 248},
    {"instance name",
     "module ch (input wire a, output wire y);\n"
     "  assign y = a;\n"
     "endmodule\n"
     "module top;\n"
     "  wire a, b;\n"
     "  ch @ (.a(a), .y(b));\n"
     "endmodule\n",
     nullptr, 248},
    {"task name",
     "module m;\n"
     "  reg [7:0] r;\n"
     "  task @; r = 8'd1; endtask\n"
     "  initial begin : blk @; end\n"
     "endmodule\n",
     nullptr, 248},
    {"function name",
     "module m;\n"
     "  reg [7:0] r;\n"
     "  function [7:0] @(input reg [7:0] n);\n"
     "    @ = n + n;\n"
     "  endfunction\n"
     "  initial r = @(8'd4);\n"
     "endmodule\n",
     IsConstructorWord, 247},
    {"gate instance name",
     "module m (input wire a, output wire y);\n"
     "  and @ (y, a, a);\n"
     "endmodule\n",
     nullptr, 248},
    {"genvar",
     "module m;\n"
     "  genvar @;\n"
     "  generate\n"
     "    for (@ = 0; @ < 2; @ = @ + 1) begin : blk\n"
     "      reg [7:0] slot;\n"
     "    end\n"
     "  endgenerate\n"
     "endmodule\n",
     nullptr, 248},
    {"named block",
     "module m;\n"
     "  reg [7:0] r;\n"
     "  initial begin : @ r = 8'd1; end\n"
     "endmodule\n",
     nullptr, 248},
    {"expression operand",
     "module m;\n"
     "  reg [7:0] r;\n"
     "  initial r = @;\n"
     "endmodule\n",
     HasOperandRoleOfItsOwn, 227},
    {"parameter name",
     "module m;\n"
     "  parameter @ = 8;\n"
     "  reg [7:0] r;\n"
     "endmodule\n",
     nullptr, 248},
    {"type name",
     "module m;\n"
     "  typedef logic [7:0] @;\n"
     "  reg [7:0] r;\n"
     "endmodule\n",
     nullptr, 248},
    {"package name",
     "package @;\n"
     "  localparam int k = 1;\n"
     "endpackage\n",
     nullptr, 248},
    {"enumeration member",
     "module m;\n"
     "  typedef enum logic [1:0] { @ } e_t;\n"
     "endmodule\n",
     nullptr, 248},
    {"port connection name",
     "module ch (input wire a, output wire y);\n"
     "  assign y = a;\n"
     "endmodule\n"
     "module top;\n"
     "  wire a, b;\n"
     "  ch u (.@(a), .y(b));\n"
     "endmodule\n",
     nullptr, 248},
};

std::string Substituted(std::string src, char mark, std::string_view word) {
  for (auto at = src.find(mark); at != std::string::npos;
       at = src.find(mark, at + 1)) {
    src.replace(at, 1, std::string(word));
  }
  return src;
}

std::string AtPosition(const Position& p, std::string_view word) {
  return Substituted(p.tmpl, '@', word);
}

constexpr const char* kControlName = "ctrl_name";

TEST(KeywordListParsing, NoReservedWordCanNameAVariable) {
  EXPECT_EQ(kReservedKeywordCount, 248u);
  for (size_t i = 0; i < kReservedKeywordCount; ++i) {
    std::string_view word = kReservedKeywords[i];
    EXPECT_FALSE(ParseOk(VarDecl(word)))
        << word << " is reserved and cannot name a variable";

    std::string free_name = std::string(word) + "_q";
    auto freed = Parse(VarDecl(free_name));
    ASSERT_NE(freed.cu, nullptr) << free_name;
    EXPECT_FALSE(freed.has_errors) << free_name;
    ASSERT_EQ(freed.cu->modules.size(), 1u) << free_name;
    EXPECT_TRUE(HasItemKindNamed(freed.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, free_name))
        << free_name << " is not reserved and names the variable";
  }
}

TEST(KeywordListParsing, NoReservedWordCanNameAnythingInAnyPosition) {
  EXPECT_EQ(std::size(kPositions), 14u);
  for (const auto& position : kPositions) {
    EXPECT_TRUE(ParseOk(AtPosition(position, kControlName)))
        << "the " << position.what << " template parses with a free name";

    size_t swept = 0;
    for (size_t i = 0; i < kReservedKeywordCount; ++i) {
      std::string_view word = kReservedKeywords[i];
      if (position.excluded != nullptr && position.excluded(word)) continue;
      ++swept;
      EXPECT_FALSE(ParseOk(AtPosition(position, word)))
          << word << " is reserved and cannot be a " << position.what;
    }
    EXPECT_EQ(swept, position.expected_swept) << position.what;
  }
}

TEST(KeywordListParsing, WordsOffTheReservedKeywordListStillNameADeclaration) {
  const char* const kNotReserved[] = {
      "randomize", "mailbox",  "semaphore", "process", "std",       "option",
      "sample",    "variable", "signal",    "entity",  "component", "wired",
      "logics",    "nettypes", "join_all",  "boolean", "unique1",   "tri2",
  };
  for (const char* word : kNotReserved) {
    for (size_t i = 0; i < kReservedKeywordCount; ++i) {
      ASSERT_NE(std::string_view(word), std::string_view(kReservedKeywords[i]))
          << word << " is on Table B.1 after all";
    }
    auto parsed = Parse(VarDecl(word));
    ASSERT_NE(parsed.cu, nullptr) << word;
    EXPECT_FALSE(parsed.has_errors) << word << " is not reserved";
    ASSERT_EQ(parsed.cu->modules.size(), 1u) << word;
    EXPECT_TRUE(HasItemKindNamed(parsed.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word << " should name the variable";
  }
}

TEST(KeywordListParsing, EscapedFormOfAReservedWordNamesAVariable) {
  size_t built = 0;
  for (size_t i = 0; i < kReservedKeywordCount; ++i) {
    std::string_view word = kReservedKeywords[i];
    std::string escaped = "\\" + std::string(word) + " ";
    auto parsed = Parse(VarDecl(escaped));
    ASSERT_NE(parsed.cu, nullptr) << word;
    EXPECT_FALSE(parsed.has_errors)
        << "\\" << word << " should name a variable";
    ASSERT_EQ(parsed.cu->modules.size(), 1u) << word;
    EXPECT_TRUE(HasItemKindNamed(parsed.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, std::string(word)))
        << "the escaped declaration should carry the spelling " << word;
    ++built;
  }
  EXPECT_EQ(built, kReservedKeywordCount)
      << "the escape works for every listed word";
}

TEST(KeywordListParsing, ReservedWordsCarryTheirOwnRoles) {
  constexpr const char* kSrc =
      "package pkg;\n"
      "  typedef enum logic [1:0] { LOW, HIGH } level_e;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } pair_t;\n"
      "endpackage\n"
      "interface iface;\n"
      "  logic ready;\n"
      "  modport source (output ready);\n"
      "endinterface\n"
      "module m (input wire clk, input wire rst, output wire [7:0] q);\n"
      "  import pkg::*;\n"
      "  localparam int unsigned kWidth = 8;\n"
      "  genvar gi;\n"
      "  pair_t split;\n"
      "  level_e level;\n"
      "  reg [kWidth-1:0] acc;\n"
      "  wire [kWidth-1:0] shadow;\n"
      "  assign shadow = acc;\n"
      "  assign q = shadow;\n"
      "  function automatic [7:0] twice(input reg [7:0] n);\n"
      "    twice = n + n;\n"
      "  endfunction\n"
      "  task automatic clear;\n"
      "    acc <= 8'd0;\n"
      "  endtask\n"
      "  always_ff @(posedge clk) begin : step\n"
      "    if (rst) clear();\n"
      "    else case (level)\n"
      "      LOW: acc <= twice(acc);\n"
      "      default: acc <= acc;\n"
      "    endcase\n"
      "  end\n"
      "  always_comb level = (acc == 8'd0) ? LOW : HIGH;\n"
      "  generate\n"
      "    for (gi = 0; gi < 2; gi = gi + 1) begin : lane\n"
      "      wire tap;\n"
      "      assign tap = shadow[gi];\n"
      "    end\n"
      "  endgenerate\n"
      "  initial begin\n"
      "    forever begin\n"
      "      repeat (2) @(posedge clk);\n"
      "      if (acc === 8'dx) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  auto parsed = Parse(kSrc);
  ASSERT_NE(parsed.cu, nullptr);
  EXPECT_FALSE(parsed.has_errors) << "keywords in their own roles must parse";
  ASSERT_EQ(parsed.cu->modules.size(), 1u);
  const auto& items = parsed.cu->modules[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kVarDecl, "acc"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kNetDecl, "shadow"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kFunctionDecl, "twice"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kTaskDecl, "clear"));
}

TEST(KeywordListParsing, EveryPositionReportsTheReservedWordOnItsLine) {
  for (const auto& position : kPositions) {
    const uint32_t kLine = LineHolding(position.tmpl, "@");
    for (size_t i = 0; i < kReservedKeywordCount; ++i) {
      std::string_view word = kReservedKeywords[i];
      if (position.excluded != nullptr && position.excluded(word)) continue;
      auto parsed = Parse(AtPosition(position, word));
      EXPECT_TRUE(ErrorOnLine(parsed.diags, kLine))
          << word << " as a " << position.what << " is reported at line "
          << kLine;
    }
  }
}

bool IsArrayMethodName(std::string_view word) {
  return word == "and" || word == "or" || word == "unique" || word == "xor";
}

bool StillAcceptedAfterADot(std::string_view word) {
  return word == "new" || word == "super";
}

bool StillAcceptedAfterAPackageScope(std::string_view word) {
  return IsArrayMethodName(word) || word == "super" || word == "this";
}

bool StillAcceptedAsACoverpointLabel(std::string_view word) {
  return word == "enum" || word == "struct" || word == "type" ||
         word == "union";
}

struct Slot {
  const char* what;
  const char* tmpl;
  uint32_t line;
  bool (*excluded)(std::string_view);
  bool (*still_accepted)(std::string_view);
  size_t expected_swept;
  const char* wire_report;
  const char* subclause;
};
constexpr Slot kSlots[] = {
    {"class name", "class %;\nendclass\n", 1, nullptr, nullptr, 248,
     "expected identifier, got 'wire'", "8.3"},
    {"class property", "class c;\n  int %;\nendclass\n", 2, nullptr, nullptr,
     248, "expected identifier, got 'wire'", "8.5"},
    {"class method",
     "class c;\n  function void %();\n  endfunction\nendclass\n", 2,
     IsConstructorWord, nullptr, 247, "expected identifier, got 'wire'",
     "13.4"},
    {"constraint name",
     "class c;\n  rand int x;\n  constraint % { x > 0; }\nendclass\n", 3,
     nullptr, nullptr, 248, "expected identifier, got 'wire'", "18.5"},
    {"interface name", "interface %;\nendinterface\n", 1, nullptr, nullptr, 248,
     "expected identifier, got 'wire'", "25.3"},
    {"modport name",
     "interface i;\n  logic a;\n  modport % (input a);\nendinterface\n", 3,
     nullptr, nullptr, 248, "expected identifier, got 'wire'", "25.5"},
    {"program name", "program %;\nendprogram\n", 1, nullptr, nullptr, 248,
     "expected identifier, got 'wire'", "24.3"},
    {"checker name", "checker %;\nendchecker\n", 1, nullptr, nullptr, 248,
     "expected identifier, got 'wire'", "17.2"},
    {"user-defined primitive name",
     "primitive % (output y, input a);\n"
     "  table\n"
     "    0 : 0;\n"
     "    1 : 1;\n"
     "  endtable\n"
     "endprimitive\n",
     1, nullptr, nullptr, 248, "expected identifier, got 'wire'", "29.3.1"},
    {"configuration name",
     "module m;\nendmodule\nconfig %;\n  design m;\nendconfig\n", 3, nullptr,
     nullptr, 248, "expected identifier, got 'wire'", "33.4.1"},
    {"net name", "module m;\n  wire %;\nendmodule\n", 2, nullptr, nullptr, 248,
     "expected identifier, got 'wire'", "6.7"},
    {"property name",
     "module m;\n  logic a;\n  property %;\n    a;\n  endproperty\n"
     "endmodule\n",
     3, nullptr, nullptr, 248, "expected identifier, got 'wire'", "16.12"},
    {"sequence name",
     "module m;\n  logic a;\n  sequence %;\n    a;\n  endsequence\n"
     "endmodule\n",
     3, nullptr, nullptr, 248, "expected identifier, got 'wire'", "16.8"},
    {"let name", "module m;\n  let % = 1;\nendmodule\n", 2, nullptr, nullptr,
     248, "expected identifier, got 'wire'", "11.12"},
    {"covergroup name", "module m;\n  covergroup %;\n  endgroup\nendmodule\n",
     2, nullptr, nullptr, 248, "expected identifier, got 'wire'", "19.3"},
    {"coverpoint name",
     "module m;\n  logic [1:0] a;\n  covergroup cg;\n    %: coverpoint a;\n"
     "  endgroup\nendmodule\n",
     4, nullptr, StillAcceptedAsACoverpointLabel, 244,
     "a covergroup item is a coverpoint, a cross or a coverage option",
     "A.2.11"},
    {"cross name",
     "module m;\n  logic [1:0] a, b;\n  covergroup cg;\n"
     "    pa: coverpoint a;\n    pb: coverpoint b;\n    %: cross pa, pb;\n"
     "  endgroup\nendmodule\n",
     6, nullptr, nullptr, 248,
     "a covergroup item is a coverpoint, a cross or a coverage option",
     "A.2.11"},
    {"clocking block name",
     "module m;\n  logic clk;\n  clocking % @(posedge clk);\n"
     "  endclocking\nendmodule\n",
     3, nullptr, nullptr, 248, "expected '@', got 'wire'", "14.3"},
    {"structure member",
     "module m;\n  struct packed { logic %; } s;\nendmodule\n", 2, nullptr,
     nullptr, 248, "expected identifier, got 'wire'", "7.2"},
    {"union member",
     "module m;\n  union packed { logic %; logic b; } u;\nendmodule\n", 2,
     nullptr, nullptr, 248, "expected identifier, got 'wire'", "7.2"},
    {"compilation-unit variable", "int %;\n", 1, nullptr, nullptr, 248,
     "expected identifier, got 'wire'", "6.8"},
    {"function local variable",
     "module m;\n  function void f();\n    int %;\n  endfunction\n"
     "endmodule\n",
     3, nullptr, nullptr, 248, "expected ';', got 'wire'", "12.3"},
    {"task local variable",
     "module m;\n  task t();\n    int %;\n  endtask\nendmodule\n", 3, nullptr,
     nullptr, 248, "expected ';', got 'wire'", "12.3"},
    {"end label of a design element", "module \\% ;\nendmodule : %\n", 2,
     nullptr, nullptr, 248, "expected identifier, got 'wire'", "9.3.4"},
    {"end label of a block",
     "module m;\n  initial begin : \\% \n  end : %\nendmodule\n", 3, nullptr,
     nullptr, 248, "expected identifier, got 'wire'", "9.3.4"},
    {"statement label",
     "module m;\n  reg r;\n  initial begin\n    %: r = 1'b1;\n  end\n"
     "endmodule\n",
     4, nullptr, nullptr, 248, "expected expression", "11.2"},
    {"attribute name", "module m;\n  (* % *) reg r;\nendmodule\n", 2, nullptr,
     nullptr, 248, "expected identifier, got 'wire'", "5.12"},
    {"hierarchical name component",
     "module ch;\n  reg r;\nendmodule\nmodule top;\n  reg x;\n  ch u ();\n"
     "  initial x = u.%;\nendmodule\n",
     7, IsArrayMethodName, StillAcceptedAfterADot, 242,
     "expected identifier, got 'wire'", "23.7"},
    {"package-scoped name",
     "package p;\n  int k;\nendpackage\nmodule m;\n  int r;\n"
     "  initial r = p::%;\nendmodule\n",
     6, IsConstructorWord, StillAcceptedAfterAPackageScope, 241,
     "expected identifier, got 'wire'", "23.7.1"},
};

std::string InSlot(const Slot& slot, std::string_view word) {
  return Substituted(slot.tmpl, '%', word);
}

TEST(KeywordListParsing, NoReservedWordCanNameAnythingInAnyScope) {
  EXPECT_EQ(std::size(kSlots), 29u);
  for (const auto& slot : kSlots) {
    auto control = Parse(InSlot(slot, kControlName));
    EXPECT_FALSE(control.has_errors)
        << "the " << slot.what << " template parses with a free name";

    size_t swept = 0;
    for (size_t i = 0; i < kReservedKeywordCount; ++i) {
      std::string_view word = kReservedKeywords[i];
      if (slot.excluded != nullptr && slot.excluded(word)) continue;
      if (slot.still_accepted != nullptr && slot.still_accepted(word)) {
        continue;
      }
      ++swept;
      auto parsed = Parse(InSlot(slot, word));
      EXPECT_TRUE(ErrorOnLine(parsed.diags, slot.line))
          << word << " is reserved and cannot be a " << slot.what;
    }
    EXPECT_EQ(swept, slot.expected_swept) << slot.what;
  }
}

TEST(KeywordListParsing, ReservedWordInEachScopeIsReportedAtIt) {
  for (const auto& slot : kSlots) {
    auto parsed = Parse(InSlot(slot, "wire"));
    EXPECT_TRUE(ReportedError(parsed.diags, slot.wire_report, slot.line,
                              slot.subclause))
        << slot.what;
  }
}

TEST(KeywordListParsing, DISABLED_ReservedWordStillAcceptedInASlotIsRejected) {
  size_t swept = 0;
  for (const auto& slot : kSlots) {
    if (slot.still_accepted == nullptr) continue;
    for (size_t i = 0; i < kReservedKeywordCount; ++i) {
      std::string_view word = kReservedKeywords[i];
      if (!slot.still_accepted(word)) continue;
      ++swept;
      auto parsed = Parse(InSlot(slot, word));
      EXPECT_TRUE(ErrorOnLine(parsed.diags, slot.line))
          << word << " is reserved and cannot be a " << slot.what;
    }
  }
  EXPECT_EQ(swept, 12u);
}

}  // namespace
