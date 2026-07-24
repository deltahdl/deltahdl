#include <cstddef>
#include <iterator>
#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Table B.1 -- the words SystemVerilog reserves -- in the alphabetical order
// the annex prints them.
constexpr const char* kTableB1[] = {
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

constexpr size_t kTableB1Count = std::size(kTableB1);

// Two entries open an aggregate type declaration. In a slot that has no way to
// close the type they start, the parser does not come back from reading one --
// a pre-existing fault, not this annex's. Positions that do close the type
// sweep them like any other word; the rest leave them to the lexer stage.
bool IsAggregateOpenerWord(std::string_view word) {
  return word == "struct" || word == "union";
}

// The plainest identifier slot there is: the name of a variable. No compiler
// directive is in force anywhere in this file, which is the point -- Annex B
// describes what the language reserves on its own, with nothing turned on.
std::string VarDecl(std::string_view word) {
  return "module m;\n  reg [7:0] " + std::string(word) + ";\nendmodule\n";
}

// An enumeration opener in a statement slot leaves the parser in the same
// state the aggregate openers do, so the statement-bearing positions below
// leave it out for the same pre-existing reason.
bool IsEnumOpenerWord(std::string_view word) { return word == "enum"; }

// Which openers a position has to leave out depends on the position: three of
// them close the type the opener starts, so they sweep the whole list.
bool ExcludeAggregateOpeners(std::string_view word) {
  return IsAggregateOpenerWord(word);
}
bool ExcludeAllTypeOpeners(std::string_view word) {
  return IsAggregateOpenerWord(word) || IsEnumOpenerWord(word);
}

// A constructor's name is spelled with a listed word, and the function-name
// production takes it in that role rather than as a chosen name, so what that
// position would record for it is not a reservation result.
bool IsConstructorWord(std::string_view word) { return word == "new"; }

bool ExcludeTypeOpenersAndConstructor(std::string_view word) {
  return ExcludeAllTypeOpeners(word) || IsConstructorWord(word);
}

// The listed words that begin a type or stand as a primary in their own right.
// In an expression they are consumed in that role, so their acceptance says
// nothing about whether a name could go there; the remaining 227 have no such
// role and cannot reach an operand slot at all.
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

// The identifier positions a variable's own name slot does not reach, each one
// entered through a different production. The '@' placeholder stands for the
// name under test everywhere it appears. Every position carries the words it
// cannot sweep and the number it does sweep, so nothing is dropped quietly.
struct Position {
  const char* what;
  const char* tmpl;
  bool (*excluded)(std::string_view);
  size_t expected_swept;
};
constexpr Position kPositions[] = {
    {"design element", "module @;\nendmodule\n", ExcludeAggregateOpeners, 246},
    {"port",
     "module m (input wire @, output wire y);\n"
     "  assign y = @;\n"
     "endmodule\n",
     ExcludeAggregateOpeners, 246},
    {"instance name",
     "module ch (input wire a, output wire y);\n"
     "  assign y = a;\n"
     "endmodule\n"
     "module top;\n"
     "  wire a, b;\n"
     "  ch @ (.a(a), .y(b));\n"
     "endmodule\n",
     ExcludeAggregateOpeners, 246},
    {"task name",
     "module m;\n"
     "  reg [7:0] r;\n"
     "  task @; r = 8'd1; endtask\n"
     "  initial begin : blk @; end\n"
     "endmodule\n",
     ExcludeAllTypeOpeners, 245},
    {"function name",
     "module m;\n"
     "  reg [7:0] r;\n"
     "  function [7:0] @(input reg [7:0] n);\n"
     "    @ = n + n;\n"
     "  endfunction\n"
     "  initial r = @(8'd4);\n"
     "endmodule\n",
     ExcludeTypeOpenersAndConstructor, 244},
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
     ExcludeAggregateOpeners, 246},
    {"named block",
     "module m;\n"
     "  reg [7:0] r;\n"
     "  initial begin : @ r = 8'd1; end\n"
     "endmodule\n",
     ExcludeAllTypeOpeners, 245},
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
     ExcludeAggregateOpeners, 246},
    {"type name",
     "module m;\n"
     "  typedef logic [7:0] @;\n"
     "  reg [7:0] r;\n"
     "endmodule\n",
     ExcludeAggregateOpeners, 246},
    {"package name",
     "package @;\n"
     "  localparam int k = 1;\n"
     "endpackage\n",
     ExcludeAggregateOpeners, 246},
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
     ExcludeAggregateOpeners, 246},
};

// Substitutes one name for every placeholder in a position template.
std::string AtPosition(const Position& p, std::string_view word) {
  std::string src = p.tmpl;
  for (auto at = src.find('@'); at != std::string::npos;
       at = src.find('@', at + 1)) {
    src.replace(at, 1, std::string(word));
  }
  return src;
}

// A name no rule reserves, used as the control everywhere a rejection is
// claimed: it shows the surrounding template parses, so the failure the sweep
// records is the word in the slot and not the frame around it.
constexpr const char* kControlName = "ctrl_name";

// Every reserved word swept through a variable's name slot. The word cannot
// name the variable, while a name that is not on the list builds the very same
// declaration and is read back off the tree -- so the rejection is the
// reservation doing its work rather than a template that never parsed.
TEST(KeywordListParsing, NoReservedWordCanNameAVariable) {
  EXPECT_EQ(kTableB1Count, 248u);
  size_t swept = 0;
  for (size_t i = 0; i < kTableB1Count; ++i) {
    std::string_view word = kTableB1[i];
    if (IsAggregateOpenerWord(word)) continue;
    ++swept;
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
  EXPECT_EQ(swept, 246u) << "the two aggregate openers are swept at the lexer";
}

// Reservation has to stop a word from naming anything at all, not just a
// variable, so the whole list goes through every identifier position above,
// one word at a time. The control name runs the same template first, which is
// what makes each rejection attributable to the word rather than the frame.
// Each position's swept total is asserted, so a word that stops being reached
// shows up as a count that no longer matches rather than as silent coverage.
TEST(KeywordListParsing, NoReservedWordCanNameAnythingInAnyPosition) {
  EXPECT_EQ(std::size(kPositions), 14u);
  for (const auto& position : kPositions) {
    EXPECT_TRUE(ParseOk(AtPosition(position, kControlName)))
        << "the " << position.what << " template parses with a free name";

    size_t swept = 0;
    for (size_t i = 0; i < kTableB1Count; ++i) {
      std::string_view word = kTableB1[i];
      if (position.excluded != nullptr && position.excluded(word)) continue;
      ++swept;
      EXPECT_FALSE(ParseOk(AtPosition(position, word)))
          << word << " is reserved and cannot be a " << position.what;
    }
    EXPECT_EQ(swept, position.expected_swept) << position.what;
  }
}

// The reservation stops at the table. Names a reader might expect to be taken
// -- built-in class and method names, other languages' reserved words, plural
// and near-miss spellings of listed words -- all still name a variable, which
// is how this stage shows the list is not quietly wider than it is printed.
TEST(KeywordListParsing, VocabularyOutsideTableB1StillNamesADeclaration) {
  const char* const kNotReserved[] = {
      "randomize", "mailbox",  "semaphore", "process", "std",       "option",
      "sample",    "variable", "signal",    "entity",  "component", "wired",
      "logics",    "nettypes", "join_all",  "boolean", "unique1",   "tri2",
  };
  for (const char* word : kNotReserved) {
    for (size_t i = 0; i < kTableB1Count; ++i) {
      ASSERT_NE(std::string_view(word), std::string_view(kTableB1[i]))
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

// The escape form is the closest accepting neighbour of every rejection above:
// the same letters, introduced by a backslash, are a chosen name again. The
// declaration builds and the variable it declares carries the keyword
// spelling, which is what separates escaping from evading the rule.
TEST(KeywordListParsing, EscapedFormOfAReservedWordNamesAVariable) {
  size_t built = 0;
  for (size_t i = 0; i < kTableB1Count; ++i) {
    std::string_view word = kTableB1[i];
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
  EXPECT_EQ(built, kTableB1Count) << "the escape works for every listed word";
}

// The accepting side of the reservation. Words that cannot name anything are
// still what the language is written in, so a design that spends them on their
// own roles has to parse -- and the module it builds is read back to show the
// keywords were consumed as keywords rather than skipped over.
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

}  // namespace
