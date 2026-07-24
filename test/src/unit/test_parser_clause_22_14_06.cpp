#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Table 22-1, the first of the three lists this version_specifier includes.
constexpr const char* kTable221[] = {
    "always",    "and",          "assign",     "begin",     "buf",
    "bufif0",    "bufif1",       "case",       "casex",     "casez",
    "cmos",      "deassign",     "default",    "defparam",  "disable",
    "edge",      "else",         "end",        "endcase",   "endfunction",
    "endmodule", "endprimitive", "endspecify", "endtable",  "endtask",
    "event",     "for",          "force",      "forever",   "fork",
    "function",  "highz0",       "highz1",     "if",        "ifnone",
    "initial",   "inout",        "input",      "integer",   "join",
    "large",     "macromodule",  "medium",     "module",    "nand",
    "negedge",   "nmos",         "nor",        "not",       "notif0",
    "notif1",    "or",           "output",     "parameter", "pmos",
    "posedge",   "primitive",    "pull0",      "pull1",     "pulldown",
    "pullup",    "rcmos",        "real",       "realtime",  "reg",
    "release",   "repeat",       "rnmos",      "rpmos",     "rtran",
    "rtranif0",  "rtranif1",     "scalared",   "small",     "specify",
    "specparam", "strong0",      "strong1",    "supply0",   "supply1",
    "table",     "task",         "time",       "tran",      "tranif0",
    "tranif1",   "tri",          "tri0",       "tri1",      "triand",
    "trior",     "trireg",       "vectored",   "wait",      "wand",
    "weak0",     "weak1",        "while",      "wire",      "wor",
    "xnor",      "xor",
};

// Table 22-2, the second included list -- included whole, the ten configuration
// words among them.
constexpr const char* kTable222[] = {
    "automatic",
    "cell",
    "config",
    "design",
    "endconfig",
    "endgenerate",
    "generate",
    "genvar",
    "incdir",
    "include",
    "instance",
    "liblist",
    "library",
    "localparam",
    "noshowcancelled",
    "pulsestyle_ondetect",
    "pulsestyle_onevent",
    "showcancelled",
    "signed",
    "unsigned",
    "use",
};

// Table 22-3, the third included list, which holds one word.
constexpr const char* kTable223[] = {
    "uwire",
};

// Table 22-4: what this version adds on top of the three lists it includes.
constexpr const char* kTable224[] = {
    "alias",         "always_comb",  "always_ff",    "always_latch",
    "assert",        "assume",       "before",       "bind",
    "bins",          "binsof",       "bit",          "break",
    "byte",          "chandle",      "class",        "clocking",
    "const",         "constraint",   "context",      "continue",
    "cover",         "covergroup",   "coverpoint",   "cross",
    "dist",          "do",           "endclass",     "endclocking",
    "endgroup",      "endinterface", "endpackage",   "endprogram",
    "endproperty",   "endsequence",  "enum",         "expect",
    "export",        "extends",      "extern",       "final",
    "first_match",   "foreach",      "forkjoin",     "iff",
    "ignore_bins",   "illegal_bins", "import",       "inside",
    "int",           "interface",    "intersect",    "join_any",
    "join_none",     "local",        "logic",        "longint",
    "matches",       "modport",      "new",          "null",
    "package",       "packed",       "priority",     "program",
    "property",      "protected",    "pure",         "rand",
    "randc",         "randcase",     "randsequence", "ref",
    "return",        "sequence",     "shortint",     "shortreal",
    "solve",         "static",       "string",       "struct",
    "super",         "tagged",       "this",         "throughout",
    "timeprecision", "timeunit",     "type",         "typedef",
    "union",         "unique",       "var",          "virtual",
    "void",          "wait_order",   "wildcard",     "with",
    "within",
};

std::string InSv2005(const std::string& body) {
  return "`begin_keywords \"1800-2005\"\n" + body + "`end_keywords\n";
}

// The three lists this version includes, used as paired legs throughout: a word
// reserved here is only *included* or *added* if there is a version under which
// the same source is accepted. "1364-2005" is the union of all three, so it is
// the leg every Table 22-4 claim is measured against.
std::string In2005(const std::string& body) {
  return "`begin_keywords \"1364-2005\"\n" + body + "`end_keywords\n";
}

std::string In2001(const std::string& body) {
  return "`begin_keywords \"1364-2001\"\n" + body + "`end_keywords\n";
}

std::string In1995(const std::string& body) {
  return "`begin_keywords \"1364-1995\"\n" + body + "`end_keywords\n";
}

std::string VarDecl(const char* word) {
  return std::string("module m;\n  reg [7:0] ") + word + ";\nendmodule\n";
}

// Two of Table 22-4's entries open an aggregate type declaration, and a
// declaration whose identifier slot holds one of them is read as the start of
// such a type. The parser does not terminate on that, with or without any
// `begin_keywords region and under the default reserved word list too, so the
// fault is not this subclause's and no test here can drive it. Both words are
// swept in the identifier slot at the lexer and preprocessor stages instead,
// where the reserved word list is observed without parsing.
bool IsAggregateOpenerWord(const std::string& word) {
  return word == "struct" || word == "union";
}

// The first included list at this stage: all 102 of Table 22-1 stay reserved,
// so none of them can occupy the identifier slot of a declaration. Sweeping the
// table whole is what makes the inclusion, rather than a handful of its
// entries, the thing being checked.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005ReservesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* word : kTable221) {
    EXPECT_FALSE(ParseWithPreprocessorOk(InSv2005(VarDecl(word))))
        << word << " is included from Table 22-1 and stays reserved";
  }
}

// The second included list, with the leg that makes it an inclusion. Each of
// Table 22-2's twenty-one entries is rejected here and accepted under
// "1364-1995", where it is not yet a keyword -- so the rejection is this
// version's list doing its work rather than an unrelated parse failure.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005ReservesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kTable222), 21u);
  for (const char* word : kTable222) {
    EXPECT_FALSE(ParseWithPreprocessorOk(InSv2005(VarDecl(word))))
        << word << " is included from Table 22-2 and is reserved here";

    auto freed = ParseWithPreprocessor(In1995(VarDecl(word)));
    ASSERT_NE(freed.cu, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    EXPECT_TRUE(HasItemKindNamed(freed.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word << " is an addition of the second included list";
  }
}

// The third included list. Its one word cannot name a variable here, names one
// under both lists the version it comes from is built on, and still opens the
// net declaration it exists for -- inclusion is about the keyword role
// surviving, not only about the identifier slot closing.
TEST(CompilerDirectiveParsing, SystemVerilog2005ReservesTheVerilog2005Word) {
  ASSERT_EQ(std::size(kTable223), 1u);
  const char* word = kTable223[0];

  EXPECT_FALSE(ParseWithPreprocessorOk(InSv2005(VarDecl(word))));

  for (const auto& earlier : {In2001(VarDecl(word)), In1995(VarDecl(word))}) {
    auto r = ParseWithPreprocessor(earlier);
    ASSERT_NE(r.cu, nullptr);
    EXPECT_FALSE(r.has_errors);
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word));
  }

  auto as_net = ParseWithPreprocessor(
      InSv2005("module m (input wire [7:0] a, output uwire [7:0] y);\n"
               "  uwire [3:0] vector_net;\n"
               "  assign y = a;\n"
               "endmodule\n"));
  ASSERT_NE(as_net.cu, nullptr);
  EXPECT_FALSE(as_net.has_errors);
  auto* m = as_net.cu->modules[0];
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[1].data_type.kind, DataTypeKind::kUwire);
  bool net_seen = false;
  for (auto* item : m->items) {
    if (item->kind == ModuleItemKind::kNetDecl && item->name == "vector_net") {
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire);
      net_seen = true;
    }
  }
  EXPECT_TRUE(net_seen);
}

// Table 22-4 swept whole in an identifier slot, with the leg that makes each
// entry an addition. The word cannot name a variable here, and under
// "1364-2005" -- the union of everything this version includes -- the very same
// declaration is built and read back off the tree. Any word for which both legs
// hold is reserved by this version_specifier and by nothing it inherits.
TEST(CompilerDirectiveParsing, SystemVerilog2005ReservesEveryWordItAdds) {
  EXPECT_EQ(std::size(kTable224), 97u);
  size_t swept = 0;
  for (const char* word : kTable224) {
    if (IsAggregateOpenerWord(word)) continue;
    EXPECT_FALSE(ParseWithPreprocessorOk(InSv2005(VarDecl(word))))
        << word << " is one of the words this version adds";

    auto freed = ParseWithPreprocessor(In2005(VarDecl(word)));
    ASSERT_NE(freed.cu, nullptr) << word;
    EXPECT_FALSE(freed.has_errors) << word;
    ASSERT_EQ(freed.cu->modules.size(), 1u) << word;
    EXPECT_TRUE(HasItemKindNamed(freed.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word << " is free under everything this version includes";
    ++swept;
  }
  EXPECT_EQ(swept, 95u);
}

// The identifier positions a variable declaration does not reach, for the three
// lists this version *includes*. Being on this version's list has to stop a
// word from naming anything at all, not just from naming a variable, so one
// word from each included table is put in turn where a design element, a port,
// an instance, a task, and a named block take their names -- five productions,
// each reached by its own path. Every one is rejected. The accepting
// counterpart is the test below, which runs the same five positions with words
// this version leaves free, so the rejections here cannot be blamed on the
// positions themselves.
//
// Table 22-4 is deliberately absent from the word list. Its position axis is
// carried by AddedWordsNameEntitiesUnderIncludedLists, which runs these same
// five templates plus three more against three added words and asserts this
// same rejection -- so listing an added word here would be a strictly weaker
// copy of what that test already does.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005ReservedWordsFillNoIdentifierPosition) {
  struct Position {
    const char* what;
    const char* tmpl;
  };
  const Position kPositions[] = {
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
      {"named block",
       "module m;\n"
       "  reg [7:0] r;\n"
       "  initial begin : @ r = 8'd1; end\n"
       "endmodule\n"},
  };

  // One word from each of the three included tables.
  const char* kReserved[] = {"wire", "generate", "uwire"};

  for (const auto& p : kPositions) {
    for (const char* word : kReserved) {
      std::string src = p.tmpl;
      for (auto at = src.find('@'); at != std::string::npos;
           at = src.find('@', at + 1)) {
        src.replace(at, 1, word);
      }
      EXPECT_FALSE(ParseWithPreprocessorOk(InSv2005(src)))
          << word << " cannot name a " << p.what << " under this version";
    }
  }
}

// The same five positions filled by words the four tables do not list, which is
// the accepting side of the bound this version's list sets. Each names its
// entity and the source parses, so the rejections above belong to the reserved
// word list rather than to anything about the positions. Three of the five are
// read back off the tree so the words are observed naming things.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005UnlistedWordsFillEveryIdentifierPosition) {
  const char* kUnlisted[] = {"checker", "let"};

  for (const char* word : kUnlisted) {
    std::string as_module = std::string("module ") + word + ";\nendmodule\n";
    auto named_module = ParseWithPreprocessor(InSv2005(as_module));
    ASSERT_NE(named_module.cu, nullptr) << word;
    EXPECT_FALSE(named_module.has_errors) << word;
    ASSERT_EQ(named_module.cu->modules.size(), 1u) << word;
    EXPECT_EQ(named_module.cu->modules[0]->name, word);

    std::string as_port = std::string("module m (input wire ") + word +
                          ", output wire y);\n  assign y = " + word +
                          ";\nendmodule\n";
    auto named_port = ParseWithPreprocessor(InSv2005(as_port));
    ASSERT_NE(named_port.cu, nullptr) << word;
    EXPECT_FALSE(named_port.has_errors) << word;
    ASSERT_EQ(named_port.cu->modules[0]->ports.size(), 2u) << word;
    EXPECT_EQ(named_port.cu->modules[0]->ports[0].name, word);

    std::string as_instance = std::string(
                                  "module ch (input wire a, output wire y);\n"
                                  "  assign y = a;\n"
                                  "endmodule\n"
                                  "module top;\n"
                                  "  wire a, b;\n"
                                  "  ch ") +
                              word + " (.a(a), .y(b));\nendmodule\n";
    auto named_instance = ParseWithPreprocessor(InSv2005(as_instance));
    ASSERT_NE(named_instance.cu, nullptr) << word;
    EXPECT_FALSE(named_instance.has_errors) << word;
    ASSERT_EQ(named_instance.cu->modules.size(), 2u) << word;
    auto* inst = FindItemByKind(named_instance.cu->modules[1]->items,
                                ModuleItemKind::kModuleInst);
    ASSERT_NE(inst, nullptr) << word;
    EXPECT_EQ(inst->inst_name, word);

    std::string as_task = std::string("module m;\n  reg [7:0] r;\n  task ") +
                          word + "; r = 8'd1; endtask\n  initial begin : blk " +
                          word + "; end\nendmodule\n";
    EXPECT_TRUE(ParseWithPreprocessorOk(InSv2005(as_task))) << word;

    std::string as_block =
        std::string("module m;\n  reg [7:0] r;\n  initial begin : ") + word +
        " r = 8'd1; end\nendmodule\n";
    EXPECT_TRUE(ParseWithPreprocessorOk(InSv2005(as_block))) << word;
  }
}

// The other side of the addition across the positions an identifier can occupy.
// The sweep above closes the variable-declaration slot for every added word and
// the test above that closes five further positions, but neither shows the
// words free in those positions under the lists this version includes -- the
// accepting leg there is carried by words a *later* standard reserves, which
// says nothing about Table 22-4. So the added words are put in each of eight
// positions under "1364-2005", the union of everything this version includes,
// where they are still ordinary identifiers. Three of the eight -- a function
// name, a gate instance name, and a genvar -- are reached by no other test
// here. Each case is paired with the same source under this version, which
// reserves the word and so admits none of them.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedWordsNameEntitiesUnderIncludedLists) {
  struct Position {
    const char* what;
    const char* tmpl;
  };
  const Position kPositions[] = {
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

  // None of these opens a design element, so the region machinery -- which
  // tracks design elements by a line's first word regardless of the list in
  // force -- stays out of the way of the sources below.
  const char* kAdded[] = {"logic", "int", "bit"};

  for (const auto& p : kPositions) {
    for (const char* word : kAdded) {
      std::string src = p.tmpl;
      for (auto at = src.find('@'); at != std::string::npos;
           at = src.find('@', at + 1)) {
        src.replace(at, 1, word);
      }
      EXPECT_TRUE(ParseWithPreprocessorOk(In2005(src)))
          << p.what << ": everything this version includes leaves " << word
          << " free";
      EXPECT_FALSE(ParseWithPreprocessorOk(InSv2005(src)))
          << p.what << ": this version reserves " << word;
    }
  }

  // Two of those positions read back, so the accepting legs are observed naming
  // things rather than merely parsing.
  auto named_module =
      ParseWithPreprocessor(In2005("module logic;\nendmodule\n"));
  ASSERT_NE(named_module.cu, nullptr);
  ASSERT_EQ(named_module.cu->modules.size(), 1u);
  EXPECT_EQ(named_module.cu->modules[0]->name, "logic");

  auto named_gate =
      ParseWithPreprocessor(In2005("module m (input wire a, output wire y);\n"
                                   "  and int (y, a, a);\n"
                                   "endmodule\n"));
  ASSERT_NE(named_gate.cu, nullptr);
  auto* gate = FindGateByKind(named_gate.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(gate, nullptr);
  EXPECT_EQ(gate->gate_inst_name, "int");
}

// The declaration forms the type test below does not reach. A declaration may
// carry its own initializer, and a port may be declared either in the header or
// in the separate style where the header lists only names and the body supplies
// direction and type. Each is a production of its own, and a word this version
// adds has to type the object in every one of them.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedTypeWordsTypeEveryDeclarationForm) {
  auto with_initializer =
      ParseWithPreprocessor(InSv2005("module m;\n"
                                     "  int   counted = 21;\n"
                                     "  byte  stepped = 8'd1;\n"
                                     "  logic [7:0] held = 8'd0;\n"
                                     "endmodule\n"));
  ASSERT_NE(with_initializer.cu, nullptr);
  EXPECT_FALSE(with_initializer.has_errors);
  const char* kInitialized[] = {"counted", "stepped", "held"};
  for (const char* name : kInitialized) {
    bool found = false;
    for (auto* item : with_initializer.cu->modules[0]->items) {
      if (item->kind != ModuleItemKind::kVarDecl || item->name != name)
        continue;
      found = true;
      // The declaration brings its own value rather than leaning on a separate
      // procedural assignment, which is what makes this a form of its own.
      EXPECT_NE(item->init_expr, nullptr) << name;
    }
    EXPECT_TRUE(found) << name;
  }

  auto ansi_ports = ParseWithPreprocessor(
      InSv2005("module ch (input logic [7:0] a, input byte b, output int y);\n"
               "  assign y = a + b;\n"
               "endmodule\n"));
  ASSERT_NE(ansi_ports.cu, nullptr);
  EXPECT_FALSE(ansi_ports.has_errors);
  auto* ch = ansi_ports.cu->modules[0];
  ASSERT_EQ(ch->ports.size(), 3u);
  EXPECT_EQ(ch->ports[0].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(ch->ports[1].data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(ch->ports[2].data_type.kind, DataTypeKind::kInt);

  auto non_ansi =
      ParseWithPreprocessor(InSv2005("module ch (a, y);\n"
                                     "  input  [7:0] a;\n"
                                     "  output [7:0] y;\n"
                                     "  logic  [7:0] y;\n"
                                     "  always_comb y = a + a;\n"
                                     "endmodule\n"));
  ASSERT_NE(non_ansi.cu, nullptr);
  EXPECT_FALSE(non_ansi.has_errors);
  auto* body_typed = non_ansi.cu->modules[0];
  ASSERT_EQ(body_typed->ports.size(), 2u);
  EXPECT_EQ(body_typed->ports[1].name, "y");
  bool typed_in_body = false;
  for (auto* item : body_typed->items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->name == "y") {
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
      typed_in_body = true;
    }
  }
  EXPECT_TRUE(typed_in_body);

  // None of the three forms can be written under the union of everything this
  // version includes, where the words introduce nothing.
  EXPECT_FALSE(
      ParseWithPreprocessorOk(In2005("module m;\n  int counted = 21;\n"
                                     "endmodule\n")));
  EXPECT_FALSE(ParseWithPreprocessorOk(
      In2005("module ch (input logic [7:0] a, output int y);\n"
             "  assign y = a;\n"
             "endmodule\n")));
  EXPECT_FALSE(
      ParseWithPreprocessorOk(In2005("module ch (a, y);\n"
                                     "  input  [7:0] a;\n"
                                     "  output [7:0] y;\n"
                                     "  logic  [7:0] y;\n"
                                     "endmodule\n")));
}

// The keyword roles the additions exist for, starting with the data types.
// Reserving a word is only half of what the version_specifier buys; the other
// half is that the word now introduces something, and each of these opens a
// declaration whose type is read back off the tree. Under "1364-2005", where
// none of them is reserved, the same source is not a set of declarations at
// all.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedTypeWordsOpenDeclarations) {
  const std::string kSrc =
      "module m;\n"
      "  logic     [7:0] a;\n"
      "  bit       [7:0] b;\n"
      "  byte            c;\n"
      "  shortint        d;\n"
      "  int             e;\n"
      "  longint         f;\n"
      "  shortreal       g;\n"
      "  string          h;\n"
      "  chandle         i;\n"
      "  var logic [7:0] j;\n"
      "  const int       k = 5;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);

  struct TypedDecl {
    const char* name;
    DataTypeKind kind;
  };
  const TypedDecl kDecls[] = {
      {"a", DataTypeKind::kLogic},     {"b", DataTypeKind::kBit},
      {"c", DataTypeKind::kByte},      {"d", DataTypeKind::kShortint},
      {"e", DataTypeKind::kInt},       {"f", DataTypeKind::kLongint},
      {"g", DataTypeKind::kShortreal}, {"h", DataTypeKind::kString},
      {"i", DataTypeKind::kChandle},   {"j", DataTypeKind::kLogic},
      {"k", DataTypeKind::kInt},
  };
  for (const auto& d : kDecls) {
    bool found = false;
    for (auto* item : r.cu->modules[0]->items) {
      if (item->kind != ModuleItemKind::kVarDecl || item->name != d.name)
        continue;
      found = true;
      EXPECT_EQ(item->data_type.kind, d.kind) << d.name;
    }
    EXPECT_TRUE(found) << d.name;
  }

  EXPECT_FALSE(ParseWithPreprocessorOk(In2005(kSrc)));
}

// The aggregate and user-defined type words, which reach the parser by a path
// of their own: `typedef` introduces a name for a type, `enum`, `struct`,
// `union` and `packed` build the types it names, and `type` appears as a
// parameter kind. The declared names are read back, and the same source under
// the union of everything this version includes is rejected.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedAggregateWordsOpenDeclarations) {
  const std::string kSrc =
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef enum {IDLE, BUSY} state_t;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } pair_t;\n"
      "  typedef union packed { logic [7:0] whole; pair_t split; } view_t;\n"
      "  byte_t  v;\n"
      "  state_t s;\n"
      "  pair_t  p;\n"
      "  view_t  u;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  for (const char* name : {"byte_t", "state_t", "pair_t", "view_t"}) {
    EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kTypedef, name))
        << name;
  }
  for (const char* name : {"v", "s", "p", "u"}) {
    bool found = false;
    for (auto* item : items) {
      if (item->kind != ModuleItemKind::kVarDecl || item->name != name)
        continue;
      found = true;
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed) << name;
    }
    EXPECT_TRUE(found) << name;
  }

  EXPECT_FALSE(ParseWithPreprocessorOk(In2005(kSrc)));
}

// The words that open a process. Each of the three inferred always forms and
// the final block is a module item of its own kind, so the tree says outright
// which word opened which -- something no identifier-slot rejection could show.
TEST(CompilerDirectiveParsing, SystemVerilog2005AddedProcessWordsOpenBlocks) {
  const std::string kSrc =
      "module m (input logic clk, input logic d, output logic q);\n"
      "  logic combo;\n"
      "  logic latched;\n"
      "  always_comb  combo = d;\n"
      "  always_ff  @(posedge clk) q <= combo;\n"
      "  always_latch if (clk) latched = d;\n"
      "  final begin end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kAlwaysCombBlock), nullptr);
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kAlwaysFFBlock), nullptr);
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kAlwaysLatchBlock), nullptr);
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kFinalBlock), nullptr);

  EXPECT_FALSE(ParseWithPreprocessorOk(In2005(kSrc)));
}

// The words that open a statement rather than a declaration or a process. The
// loop-control and return statements, the do-while and foreach loops, and the
// case qualifiers are all reached through a procedural block, which is a path
// of its own. The statement kinds are read back off the initial block's body.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedStatementWordsOpenStatements) {
  const std::string kSrc =
      "module m;\n"
      "  int  arr [0:3];\n"
      "  int  i;\n"
      "  int  total;\n"
      "  logic [1:0] sel;\n"
      "  function int twice(input int n);\n"
      "    return n + n;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    do total = total + 1; while (total < 2);\n"
      "    foreach (arr[j]) total = total + 1;\n"
      "    for (i = 0; i < 4; i = i + 1) begin\n"
      "      if (i == 1) continue;\n"
      "      if (i == 3) break;\n"
      "    end\n"
      "    unique case (sel) 2'b01: total = 1; default: total = 0; endcase\n"
      "    priority case (sel) 2'b01: total = 2; default: total = 0; endcase\n"
      "    if (sel inside {2'b01, 2'b10}) total = twice(3);\n"
      "  end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto* init =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(init, nullptr);
  ASSERT_NE(init->body, nullptr);

  auto has_kind = [](Stmt* block, StmtKind kind) {
    for (auto* s : block->stmts) {
      if (s != nullptr && s->kind == kind) return true;
    }
    return false;
  };
  EXPECT_TRUE(has_kind(init->body, StmtKind::kDoWhile));
  EXPECT_TRUE(has_kind(init->body, StmtKind::kForeach));

  auto* fn =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kFunctionDecl);
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(fn->name, "twice");

  EXPECT_FALSE(ParseWithPreprocessorOk(In2005(kSrc)));
}

// The words that open a design element, which is the outermost syntactic
// position any of the additions reaches. An interface with a modport, a package
// with a constant that is then imported, a program, and a class hierarchy each
// land in their own list on the compilation unit, so what opened them is read
// back rather than inferred from the source parsing.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedDesignElementWordsOpenElements) {
  const std::string kSrc =
      "package pkg;\n"
      "  localparam int WIDTH = 8;\n"
      "endpackage\n"
      "interface ifc;\n"
      "  logic [7:0] data;\n"
      "  modport source (output data);\n"
      "endinterface\n"
      "program prg;\n"
      "  initial begin end\n"
      "endprogram\n"
      "class base;\n"
      "  int v;\n"
      "  function new(); v = 1; endfunction\n"
      "endclass\n"
      "class derived extends base;\n"
      "  virtual function void bump(); this.v = super.v + 1; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  import pkg::*;\n"
      "  logic [7:0] w;\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "prg");
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->name, "base");
  EXPECT_EQ(r.cu->classes[1]->name, "derived");

  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_NE(
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kImportDecl),
      nullptr);

  EXPECT_FALSE(ParseWithPreprocessorOk(In2005(kSrc)));
}

// The verification vocabulary, which is the part of Table 22-4 with no Verilog
// ancestor at all: an immediate assertion, a named property and sequence, a
// cover statement, a covergroup with a coverpoint and its bins, a clocking
// block, and the fork-join variants. Each lands as its own module item.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005AddedVerificationWordsOpenConstructs) {
  const std::string kSrc =
      "module m (input logic clk, input logic req, input logic ack);\n"
      "  logic [7:0] count;\n"
      "  property p_handshake;\n"
      "    @(posedge clk) req |-> ack;\n"
      "  endproperty\n"
      "  sequence s_pulse;\n"
      "    @(posedge clk) req;\n"
      "  endsequence\n"
      "  clocking cb @(posedge clk);\n"
      "    input req;\n"
      "  endclocking\n"
      "  covergroup cg @(posedge clk);\n"
      "    cp_count: coverpoint count {\n"
      "      bins low  = {0};\n"
      "      bins high = {255};\n"
      "    }\n"
      "  endgroup\n"
      "  initial begin\n"
      "    assert (count == 8'd0);\n"
      "    fork\n"
      "      count = 8'd1;\n"
      "    join_none\n"
      "    fork\n"
      "      count = 8'd2;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(
      HasItemKindNamed(items, ModuleItemKind::kPropertyDecl, "p_handshake"));
  EXPECT_TRUE(
      HasItemKindNamed(items, ModuleItemKind::kSequenceDecl, "s_pulse"));
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kClockingBlock), nullptr);
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kCovergroupDecl, "cg"));

  EXPECT_FALSE(ParseWithPreprocessorOk(In2005(kSrc)));
}

// Table 22-1 in its keyword role under this version: inclusion is not only
// about what a word may no longer name. The gate primitives build structure,
// the resolved net types and drive strengths are written out, and the
// procedural statements build control flow -- all under a region opened for
// this version_specifier.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005IncludedVerilog1995WordsStillWork) {
  auto r = ParseWithPreprocessor(
      InSv2005("module m (input wire a, inout wire b, output wire y);\n"
               "  wand   w;\n"
               "  trireg (small) cap;\n"
               "  supply0 gnd;\n"
               "  integer i;\n"
               "  real    r;\n"
               "  time    t;\n"
               "  event   e;\n"
               "  reg [1:0] sel;\n"
               "  and  g1 (y, a, b);\n"
               "  nmos g2 (w, a, b);\n"
               "  initial begin\n"
               "    for (i = 0; i < 2; i = i + 1) r = r + 1.0;\n"
               "    repeat (2) t = t + 1;\n"
               "    while (i > 0) i = i - 1;\n"
               "    casez (sel)\n"
               "      2'b1?: i = 1;\n"
               "      default: i = 0;\n"
               "    endcase\n"
               "    -> e;\n"
               "  end\n"
               "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kNetDecl, "w"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kVarDecl, "i"));

  auto* gate = FindGateByKind(items, GateKind::kAnd);
  ASSERT_NE(gate, nullptr);
  EXPECT_EQ(gate->gate_inst_name, "g1");
  EXPECT_NE(FindGateByKind(items, GateKind::kNmos), nullptr);
}

// Including Table 22-2 means including the ten words a configuration is written
// with, which is the sharpest thing that list contributes: seven of them appear
// here and the declaration is built. Under "1364-1995", the first of the three
// lists this version includes, none of the words is reserved and the construct
// cannot be written -- so the configuration exists here because of the second
// inclusion and not by default.
TEST(CompilerDirectiveParsing, SystemVerilog2005IncludesTheConfigurationWords) {
  const std::string kSrc =
      "module top;\n"
      "endmodule\n"
      "config config_a;\n"
      "  design top;\n"
      "  default liblist blue green;\n"
      "  instance top.u1 liblist red;\n"
      "  cell m1 use lib.m2;\n"
      "endconfig\n";

  auto r = ParseWithPreprocessor(InSv2005(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto* cfg = r.cu->configs[0];
  EXPECT_EQ(cfg->name, "config_a");
  // One rule per clause below the design statement: the default liblist, the
  // instance rule, and the cell rule.
  EXPECT_EQ(cfg->rules.size(), 3u);

  EXPECT_FALSE(ParseWithPreprocessorOk(In1995(kSrc)));

  // The module alongside it parses under both, so the rejection above belongs
  // to the configuration rather than to the source as a whole.
  EXPECT_TRUE(ParseWithPreprocessorOk(In1995("module top;\nendmodule\n")));
}

// The rest of Table 22-2 in its keyword role. `localparam` declares a constant,
// `genvar`/`generate`/`endgenerate` build a loop generate construct,
// `automatic` qualifies a subroutine, `signed` and `unsigned` qualify
// declarations, and the four pulse-control words are specify items -- each the
// construct its word exists to open, all still available under this version.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005IncludedVerilog2001WordsStillWork) {
  auto r = ParseWithPreprocessor(
      InSv2005("module m (input wire a, output wire y);\n"
               "  localparam L = 2;\n"
               "  genvar g;\n"
               "  reg signed   [7:0] s;\n"
               "  reg unsigned [7:0] u;\n"
               "  generate\n"
               "    for (g = 0; g < L; g = g + 1) begin : blk\n"
               "      reg [7:0] slot;\n"
               "    end\n"
               "  endgenerate\n"
               "  function automatic [7:0] twice(input reg [7:0] n);\n"
               "    twice = n + n;\n"
               "  endfunction\n"
               "  assign y = a;\n"
               "  specify\n"
               "    pulsestyle_ondetect y;\n"
               "    pulsestyle_onevent y;\n"
               "    showcancelled y;\n"
               "    noshowcancelled y;\n"
               "    (a => y) = 1;\n"
               "  endspecify\n"
               "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kParamDecl, "L"));
  EXPECT_TRUE(HasItemKindNamed(items, ModuleItemKind::kFunctionDecl, "twice"));
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kGenerateFor), nullptr);
  EXPECT_NE(FindSpecifyBlock(items), nullptr);

  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->name == "s") {
      EXPECT_TRUE(item->data_type.is_signed);
    }
    if (item->kind == ModuleItemKind::kVarDecl && item->name == "u") {
      EXPECT_FALSE(item->data_type.is_signed);
    }
  }
}

// The negative the four tables imply, at the stage where it shows: a word none
// of them lists is an ordinary identifier under this version, so it names
// things freely and opens nothing. Both halves are here -- the same word naming
// a declaration and failing to be a data type -- because either one alone would
// leave the other unchecked.
TEST(CompilerDirectiveParsing,
     SystemVerilog2005LeavesUnlistedWordsAsIdentifiers) {
  // None of these opens a design element, so putting one at the head of a line
  // leaves the region machinery -- which tracks design elements by a line's
  // first word, without regard to the list in force -- out of the picture, and
  // the only thing that can reject the source is the word not being a type.
  const char* kUnlisted[] = {"until", "let", "global", "nettype", "soft"};
  for (const char* word : kUnlisted) {
    auto r = ParseWithPreprocessor(InSv2005(VarDecl(word)));
    ASSERT_NE(r.cu, nullptr) << word;
    EXPECT_FALSE(r.has_errors) << word;
    ASSERT_EQ(r.cu->modules.size(), 1u) << word;
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word;

    std::string as_type =
        std::string("module m;\n  ") + word + " [7:0] v;\nendmodule\n";
    EXPECT_FALSE(ParseWithPreprocessorOk(InSv2005(as_type)))
        << word << " is not a data type under this version";
  }
}

}  // namespace
