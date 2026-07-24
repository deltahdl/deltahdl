#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Table 22-1, the first of the two lists this version_specifier includes.
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

// Table 22-2, the second list, included whole -- the ten configuration words
// among them.
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

// Table 22-3: what this version adds on its own.
constexpr const char* kTable223[] = {
    "uwire",
};

std::string In2005(const std::string& body) {
  return "`begin_keywords \"1364-2005\"\n" + body + "`end_keywords\n";
}

// The two lists this version includes, used as paired legs throughout: a word
// reserved here is only *included* or *added* if there is a version under which
// the same source is accepted.
std::string In2001(const std::string& body) {
  return "`begin_keywords \"1364-2001\"\n" + body + "`end_keywords\n";
}

std::string In1995(const std::string& body) {
  return "`begin_keywords \"1364-1995\"\n" + body + "`end_keywords\n";
}

std::string VarDecl(const char* word) {
  return std::string("module m;\n  reg [7:0] ") + word + ";\nendmodule\n";
}

// The first included list at this stage: all 102 of Table 22-1 stay reserved,
// so none of them can occupy the identifier slot of a declaration. Sweeping the
// table whole is what makes the inclusion, rather than a handful of its
// entries, the thing being checked.
TEST(CompilerDirectiveParsing, Verilog2005ReservesEveryVerilog1995Keyword) {
  EXPECT_EQ(std::size(kTable221), 102u);
  for (const char* word : kTable221) {
    EXPECT_FALSE(ParseWithPreprocessorOk(In2005(VarDecl(word))))
        << word << " is included from Table 22-1 and stays reserved";
  }
}

// The second included list, with the leg that makes it an inclusion. Each of
// Table 22-2's twenty-one entries is rejected here and accepted under
// "1364-1995", where it is not yet a keyword -- so the rejection is this
// version's list doing its work rather than an unrelated parse failure.
TEST(CompilerDirectiveParsing, Verilog2005ReservesEveryVerilog2001Keyword) {
  EXPECT_EQ(std::size(kTable222), 21u);
  for (const char* word : kTable222) {
    EXPECT_FALSE(ParseWithPreprocessorOk(In2005(VarDecl(word))))
        << word << " is included from Table 22-2 and is reserved here";
    EXPECT_TRUE(ParseWithPreprocessorOk(In1995(VarDecl(word))))
        << word << " is an addition of the later of the two included lists";
  }
}

// The identifier positions a variable declaration does not reach. Being on this
// version's list has to stop a word from naming anything at all, not just from
// naming a variable, so words drawn from each of the three tables are put in
// turn where a design element, a port, an instance, a task, and a named block
// take their names -- five productions, each reached by its own path. Every one
// is rejected. The accepting counterpart is the test below, which runs the same
// five positions with a word this version leaves free, so the rejections here
// cannot be blamed on the positions themselves.
TEST(CompilerDirectiveParsing,
     Verilog2005ReservedWordsFillNoIdentifierPosition) {
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

  // One word from each table, so all three legs of the list are represented in
  // every position rather than only the inherited ones.
  const char* kReserved[] = {"wire", "generate", "uwire"};

  for (const auto& p : kPositions) {
    for (const char* word : kReserved) {
      std::string src = p.tmpl;
      for (auto at = src.find('@'); at != std::string::npos;
           at = src.find('@', at + 1)) {
        src.replace(at, 1, word);
      }
      EXPECT_FALSE(ParseWithPreprocessorOk(In2005(src)))
          << word << " cannot name a " << p.what << " under this version";
    }
  }
}

// The same five positions filled by words the three tables do not list, which
// is the accepting side of the bound this version's list sets. Each names its
// entity and the source parses, so the rejections above belong to the reserved
// word list rather than to anything about the positions. Two of the five are
// read back off the tree so the words are observed naming things.
TEST(CompilerDirectiveParsing,
     Verilog2005UnlistedWordsFillEveryIdentifierPosition) {
  const char* kUnlisted[] = {"logic", "bit"};

  for (const char* word : kUnlisted) {
    std::string as_module = std::string("module ") + word + ";\nendmodule\n";
    auto named_module = ParseWithPreprocessor(In2005(as_module));
    ASSERT_NE(named_module.cu, nullptr) << word;
    EXPECT_FALSE(named_module.has_errors) << word;
    ASSERT_EQ(named_module.cu->modules.size(), 1u) << word;
    EXPECT_EQ(named_module.cu->modules[0]->name, word);

    std::string as_port = std::string("module m (input wire ") + word +
                          ", output wire y);\n  assign y = " + word +
                          ";\nendmodule\n";
    auto named_port = ParseWithPreprocessor(In2005(as_port));
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
    auto named_instance = ParseWithPreprocessor(In2005(as_instance));
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
    EXPECT_TRUE(ParseWithPreprocessorOk(In2005(as_task))) << word;

    std::string as_block =
        std::string("module m;\n  reg [7:0] r;\n  initial begin : ") + word +
        " r = 8'd1; end\nendmodule\n";
    EXPECT_TRUE(ParseWithPreprocessorOk(In2005(as_block))) << word;
  }
}

// Table 22-3, and what makes it an addition rather than an inheritance: the one
// word it holds cannot name a variable here, and names one under both of the
// lists this version includes. The accepting legs are read back off the parsed
// tree, so the word is observed naming something rather than merely getting
// past the lexer.
TEST(CompilerDirectiveParsing, Verilog2005ReservesTheWordItAddsItself) {
  ASSERT_EQ(std::size(kTable223), 1u);
  const char* added = kTable223[0];

  EXPECT_FALSE(ParseWithPreprocessorOk(In2005(VarDecl(added))));

  for (const auto& earlier : {In2001(VarDecl(added)), In1995(VarDecl(added))}) {
    auto r = ParseWithPreprocessor(earlier);
    ASSERT_NE(r.cu, nullptr);
    EXPECT_FALSE(r.has_errors);
    ASSERT_EQ(r.cu->modules.size(), 1u);
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, added));
  }
}

// The added word in its keyword role, which is where the addition has its
// point: it opens a net declaration. Every form the declaration takes is here
// -- a scalar, a vector, a signed vector, and a port -- because each reaches
// the parser by its own path, and each is read back as the net type the word
// names. The same source under the later of the two included lists cannot be
// written at all, since there the word is just an identifier.
TEST(CompilerDirectiveParsing, Verilog2005AddedWordOpensANetDeclaration) {
  auto r = ParseWithPreprocessor(
      In2005("module m (input wire [7:0] a, output uwire [7:0] y);\n"
             "  uwire        scalar_net;\n"
             "  uwire [3:0]  vector_net;\n"
             "  uwire signed [7:0] signed_net;\n"
             "  assign y = a;\n"
             "endmodule\n"));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);

  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->ports.size(), 2u);
  EXPECT_EQ(m->ports[1].name, "y");
  EXPECT_EQ(m->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(m->ports[1].data_type.kind, DataTypeKind::kUwire);

  const char* kNets[] = {"scalar_net", "vector_net", "signed_net"};
  for (const char* name : kNets) {
    bool found = false;
    for (auto* item : m->items) {
      if (item->kind != ModuleItemKind::kNetDecl || item->name != name)
        continue;
      found = true;
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire) << name;
    }
    EXPECT_TRUE(found) << name;
  }

  bool signed_seen = false;
  for (auto* item : m->items) {
    if (item->kind == ModuleItemKind::kNetDecl && item->name == "signed_net") {
      EXPECT_TRUE(item->data_type.is_signed);
      signed_seen = true;
    }
  }
  EXPECT_TRUE(signed_seen);

  // Under the list this version extends the same declarations are not
  // declarations at all.
  EXPECT_FALSE(
      ParseWithPreprocessorOk(In2001("module m;\n"
                                     "  uwire scalar_net;\n"
                                     "endmodule\n")));
}

// The declaration forms the test above does not reach. A net declaration may
// carry its own assignment, and a port may be declared in the separate style
// where the header lists only names and the body gives each one its direction
// and its type -- both are productions of their own, and the added word has to
// open the net in each. The paired legs reject the same sources under the later
// of the two included lists, where the word introduces nothing.
TEST(CompilerDirectiveParsing, Verilog2005AddedWordTypesEveryDeclarationForm) {
  auto with_assignment =
      ParseWithPreprocessor(In2005("module m;\n"
                                   "  reg   [7:0] src;\n"
                                   "  uwire [7:0] bus = src + 8'd1;\n"
                                   "endmodule\n"));
  ASSERT_NE(with_assignment.cu, nullptr);
  EXPECT_FALSE(with_assignment.has_errors);
  bool bus_seen = false;
  for (auto* item : with_assignment.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kNetDecl || item->name != "bus") continue;
    bus_seen = true;
    EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire);
    // The declaration carries its driver rather than leaning on a separate
    // continuous assignment, which is what makes this a form of its own.
    EXPECT_NE(item->init_expr, nullptr);
  }
  EXPECT_TRUE(bus_seen);

  auto non_ansi =
      ParseWithPreprocessor(In2005("module ch (a, y);\n"
                                   "  input  [7:0] a;\n"
                                   "  output [7:0] y;\n"
                                   "  uwire  [7:0] y;\n"
                                   "  assign y = a;\n"
                                   "endmodule\n"));
  ASSERT_NE(non_ansi.cu, nullptr);
  EXPECT_FALSE(non_ansi.has_errors);
  auto* ch = non_ansi.cu->modules[0];
  ASSERT_EQ(ch->ports.size(), 2u);
  EXPECT_EQ(ch->ports[1].name, "y");
  bool typed_in_body = false;
  for (auto* item : ch->items) {
    if (item->kind == ModuleItemKind::kNetDecl && item->name == "y") {
      EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire);
      typed_in_body = true;
    }
  }
  EXPECT_TRUE(typed_in_body);

  EXPECT_FALSE(
      ParseWithPreprocessorOk(In2001("module m;\n"
                                     "  reg   [7:0] src;\n"
                                     "  uwire [7:0] bus = src + 8'd1;\n"
                                     "endmodule\n")));
  EXPECT_FALSE(
      ParseWithPreprocessorOk(In2001("module ch (a, y);\n"
                                     "  input  [7:0] a;\n"
                                     "  output [7:0] y;\n"
                                     "  uwire  [7:0] y;\n"
                                     "endmodule\n")));
}

// The other side of the addition across the positions an identifier can occupy.
// A declaration is only the most obvious one, so the word this version adds is
// put in each of the rest -- naming a design element, a port, an instance, a
// task, a function, a gate instance, and a genvar -- under the later of the two
// lists this version includes, where it is still an ordinary identifier. Each
// case is paired with the same source under this version, which reserves the
// word and so admits none of them.
TEST(CompilerDirectiveParsing, Verilog2005AddedWordNamesEntitiesUnderEarlier) {
  struct Position {
    const char* what;
    const char* src;
  };
  const Position kPositions[] = {
      {"design element", "module uwire;\nendmodule\n"},
      {"port",
       "module m (input wire uwire, output wire y);\n"
       "  assign y = uwire;\n"
       "endmodule\n"},
      {"instance",
       "module ch (input wire a, output wire y);\n"
       "  assign y = a;\n"
       "endmodule\n"
       "module top;\n"
       "  wire a, b;\n"
       "  ch uwire (.a(a), .y(b));\n"
       "endmodule\n"},
      {"task",
       "module m;\n"
       "  reg [7:0] r;\n"
       "  task uwire; r = 8'd1; endtask\n"
       "  initial begin : blk uwire; end\n"
       "endmodule\n"},
      {"function",
       "module m;\n"
       "  reg [7:0] r;\n"
       "  function [7:0] uwire(input reg [7:0] n);\n"
       "    uwire = n + n;\n"
       "  endfunction\n"
       "  initial r = uwire(8'd4);\n"
       "endmodule\n"},
      {"gate instance",
       "module m (input wire a, output wire y);\n"
       "  and uwire (y, a, a);\n"
       "endmodule\n"},
      {"genvar",
       "module m;\n"
       "  genvar uwire;\n"
       "  generate\n"
       "    for (uwire = 0; uwire < 2; uwire = uwire + 1) begin : blk\n"
       "      reg [7:0] slot;\n"
       "    end\n"
       "  endgenerate\n"
       "endmodule\n"},
  };

  for (const auto& p : kPositions) {
    EXPECT_TRUE(ParseWithPreprocessorOk(In2001(p.src)))
        << p.what << ": the earlier list leaves this word free";
    EXPECT_FALSE(ParseWithPreprocessorOk(In2005(p.src)))
        << p.what << ": this version reserves it";
  }

  // Two of those positions read back, so the accepting legs are observed
  // naming things rather than merely parsing.
  auto named_module = ParseWithPreprocessor(In2001(kPositions[0].src));
  ASSERT_NE(named_module.cu, nullptr);
  ASSERT_EQ(named_module.cu->modules.size(), 1u);
  EXPECT_EQ(named_module.cu->modules[0]->name, "uwire");

  auto named_instance = ParseWithPreprocessor(In2001(kPositions[2].src));
  ASSERT_NE(named_instance.cu, nullptr);
  ASSERT_EQ(named_instance.cu->modules.size(), 2u);
  auto* inst = FindItemByKind(named_instance.cu->modules[1]->items,
                              ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_name, "uwire");
}

// Including Table 22-2 whole means including the ten words a configuration is
// written with, which is the sharpest thing that list contributes: seven of
// them appear here and the declaration is built. Under "1364-1995", the other
// list this version includes, none of the words is reserved and the construct
// cannot be written -- so the configuration exists here because of the second
// inclusion and not by default.
TEST(CompilerDirectiveParsing, Verilog2005IncludesTheConfigurationWords) {
  const std::string kSrc =
      "module top;\n"
      "endmodule\n"
      "config config_a;\n"
      "  design top;\n"
      "  default liblist blue green;\n"
      "  instance top.u1 liblist red;\n"
      "  cell m1 use lib.m2;\n"
      "endconfig\n";

  auto r = ParseWithPreprocessor(In2005(kSrc));
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

// The rest of Table 22-2 in its keyword role rather than in an identifier slot.
// `localparam` declares a constant, `genvar`/`generate`/`endgenerate` build a
// loop generate construct, `automatic` qualifies a subroutine, `signed` and
// `unsigned` qualify declarations, and the four pulse-control words are specify
// items -- each the construct its word exists to open.
TEST(CompilerDirectiveParsing,
     Verilog2005IncludedAdditionsOpenTheirConstructs) {
  auto r = ParseWithPreprocessor(
      In2005("module m (input wire a, output wire y);\n"
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

// Table 22-1 in its keyword role too: inclusion is not only about what a word
// may no longer name. The gate primitives build structure, the resolved net
// types and drive strengths are written out, and the procedural statements
// build control flow -- all of it under a region opened for this version.
TEST(CompilerDirectiveParsing, Verilog2005IncludedVerilog1995WordsStillWork) {
  auto r = ParseWithPreprocessor(
      In2005("module m (input wire a, inout wire b, output wire y);\n"
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

// The negative the three tables imply, at the stage where it shows: a word none
// of them lists is an ordinary identifier under this version, so it names
// things freely and opens nothing. Both halves are here -- the same word naming
// a declaration and failing to be a data type -- because either one alone would
// leave the other unchecked.
TEST(CompilerDirectiveParsing, Verilog2005LeavesUnlistedWordsAsIdentifiers) {
  const char* kUnlisted[] = {"logic", "interface", "bit", "byte", "int"};
  for (const char* word : kUnlisted) {
    auto r = ParseWithPreprocessor(In2005(VarDecl(word)));
    ASSERT_NE(r.cu, nullptr) << word;
    EXPECT_FALSE(r.has_errors) << word;
    ASSERT_EQ(r.cu->modules.size(), 1u) << word;
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word;

    std::string as_type =
        std::string("module m;\n  ") + word + " [7:0] v;\nendmodule\n";
    EXPECT_FALSE(ParseWithPreprocessorOk(In2005(as_type)))
        << word << " is not a data type under this version";
  }
}

}  // namespace
