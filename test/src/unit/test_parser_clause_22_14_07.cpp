#include <cstddef>
#include <iterator>
#include <string>

#include "fixture_parser.h"
#include "helpers_identifier_position_sweep.h"
#include "helpers_included_keyword_parse.h"
#include "helpers_keyword_sweep_skips.h"
#include "helpers_keyword_version.h"
#include "helpers_parser_verify.h"
#include "model_identifier_positions.h"
#include "model_keyword_tables.h"

using namespace delta;

namespace {
// The first included list at this stage: all 102 of Table 22-1 stay reserved,
// so none of them can occupy the identifier slot of a declaration. Sweeping the
// table whole is what makes the inclusion, rather than a handful of its
// entries, the thing being checked.
TEST(CompilerDirectiveParsing,
     SystemVerilog2009ReservesEveryVerilog1995Keyword) {
  ExpectKeywordTableIsReservedAtParse("1800-2009", kSweepTable221AtParse);
}

// The second included list, with the leg that makes it an inclusion. Each of
// Table 22-2's twenty-one entries is rejected here and accepted under
// "1364-1995", where it is not yet a keyword -- so the rejection is this
// version's list doing its work rather than an unrelated parse failure. The ten
// configuration words carry a second accepting leg under the configuration-free
// companion list, which drops exactly them: that is how this stage shows the
// version inherits "1364-2001" whole rather than its reduced companion.
TEST(CompilerDirectiveParsing,
     SystemVerilog2009ReservesEveryVerilog2001Keyword) {
  ExpectKeywordTableIsReservedAtParse("1800-2009", kSweepTable222);
  ExpectConfigurationWordsNameVariablesAtParse();
}

// The third included list. Its one word cannot name a variable here, names one
// under both lists the version it comes from is built on, and still opens the
// net declaration it exists for -- inclusion is about the keyword role
// surviving, not only about the identifier slot closing.
TEST(CompilerDirectiveParsing, SystemVerilog2009ReservesTheVerilog2005Word) {
  ExpectKeywordTableIsReservedAtParse("1800-2009", kSweepTable223);
  ExpectUwireStillOpensNetDeclarations("1800-2009");
}

// The fourth included list swept whole in an identifier slot. Each entry is
// rejected here and, under "1364-2005" -- the union of the three lists that one
// is itself built on -- names a variable that is read back off the tree, so the
// inclusion is traced to the fourth list rather than to anything earlier.
TEST(CompilerDirectiveParsing,
     SystemVerilog2009ReservesEverySystemVerilog2005Keyword) {
  ExpectKeywordTableIsReservedAtParse("1800-2009", kSweepTable224);
}

// Table 22-5 swept whole in an identifier slot, with the leg that makes each
// entry an addition. The word cannot name a variable here, and under
// "1800-2005" -- the union of everything this version includes -- the very same
// declaration is built and read back off the tree. Any word for which both legs
// hold is reserved by this version_specifier and by nothing it inherits.
TEST(CompilerDirectiveParsing, SystemVerilog2009ReservesEveryWordItAdds) {
  ExpectKeywordTableIsReservedAtParse("1800-2009", kSweepTable225);
}

// The identifier positions a variable declaration does not reach, for the four
// lists this version *includes*. Being on this version's list has to stop a
// word from naming anything at all, not just from naming a variable, so one
// word from each included table is put in turn where a design element, a port,
// an instance, a task, and a named block take their names -- five productions,
// each reached by its own path. Every one is rejected.
//
// Table 22-5 is deliberately absent from the word list here. Its position axis
// is carried by AddedWordsNameEntitiesUnderIncludedLists below, which runs
// these same five templates plus three more against three added words and
// asserts this same rejection alongside its accepting counterpart -- so listing
// an added word here would be a strictly weaker copy of that.
TEST(CompilerDirectiveParsing,
     SystemVerilog2009ReservedWordsFillNoIdentifierPosition) {
  ExpectWordsFillNoIdentifierPosition(
      "1800-2009", {"wire", "generate", "uwire", "logic"},
      {"design element", "port", "instance", "task", "named block"});
}

// The other side of the addition across the positions an identifier can occupy.
// The sweep above closes the variable-declaration slot for every added word,
// but it does not show the words free in any *other* position under the lists
// this version includes. So the added words are put in each of eight positions
// under "1800-2005", the union of everything this version includes, where they
// are still ordinary identifiers -- a design element, a port, an instance, a
// task, a function, a gate instance, a genvar, and a named block. Each case is
// paired with the same source under this version, which reserves the word and
// so admits none of them.
TEST(CompilerDirectiveParsing,
     SystemVerilog2009AddedWordsNameEntitiesUnderIncludedLists) {
  ExpectWordsNameEntitiesUnder("1800-2005", "1800-2009",
                               {"until", "weak", "unique0"});

  // Two of those positions read back, so the accepting legs are observed naming
  // things rather than merely parsing.
  auto named_module =
      ParseWithPreprocessor(InSv2005("module until;\nendmodule\n"));
  ASSERT_NE(named_module.cu, nullptr);
  ASSERT_EQ(named_module.cu->modules.size(), 1u);
  EXPECT_EQ(named_module.cu->modules[0]->name, "until");

  auto named_gate =
      ParseWithPreprocessor(InSv2005("module m (input wire a, output wire y);\n"
                                     "  and weak (y, a, a);\n"
                                     "endmodule\n"));
  ASSERT_NE(named_gate.cu, nullptr);
  auto* gate = FindGateByKind(named_gate.cu->modules[0]->items, GateKind::kAnd);
  ASSERT_NE(gate, nullptr);
  EXPECT_EQ(gate->gate_inst_name, "weak");
}

// The first of the keyword roles the additions exist for. `checker` and
// `endchecker` bracket a design element of their own -- the only added word
// pair that does -- and it lands in the compilation unit's own list of them,
// separate from its modules. The checker's body is written with the assertion
// vocabulary of the fourth included list, so the construct also shows the
// inclusion and the addition working together.
TEST(CompilerDirectiveParsing, SystemVerilog2009AddedCheckerOpensAnElement) {
  const std::string kSrc =
      "checker handshake (logic clk, logic req);\n"
      "  assert property (@(posedge clk) req);\n"
      "endchecker\n"
      "module m;\n"
      "  logic clk;\n"
      "  logic req;\n"
      "  handshake u_chk (clk, req);\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2009(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "handshake");
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");

  EXPECT_FALSE(ParseWithPreprocessorOk(InSv2005(kSrc)));
}

// The `let` declaration, which is the added word with the widest position axis:
// it may be written at the compilation unit's own scope, inside a design
// element, inside a clocking block, and as a block item among statements. Each
// is a production of its own and none of the others reaches it, so all four are
// here. `untyped`, the other added word this construct admits, types -- or
// rather declines to type -- a formal argument, and the declaration is read
// back to show which formal was left untyped and which was not.
TEST(CompilerDirectiveParsing, SystemVerilog2009AddedLetOpensDeclarations) {
  const std::string kSrc =
      "let gain = 21;\n"
      "module m (input logic clk);\n"
      "  logic [7:0] a, b, r;\n"
      "  let sum(untyped x, int y) = x + y;\n"
      "  clocking cb @(posedge clk);\n"
      "    let half = 4;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    let inner(untyped z) = z + z;\n"
      "    r = inner(a) + sum(a, b) + gain;\n"
      "  end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2009(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  // The compilation-unit scope form.
  bool cu_let_seen = false;
  for (auto* item : r.cu->cu_items) {
    if (item->kind == ModuleItemKind::kLetDecl && item->name == "gain") {
      EXPECT_NE(item->init_expr, nullptr);
      cu_let_seen = true;
    }
  }
  EXPECT_TRUE(cu_let_seen);

  // The design-element form, with the untyped formal alongside a typed one.
  auto& items = r.cu->modules[0]->items;
  auto* sum = FindItemByKind(items, ModuleItemKind::kLetDecl);
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(sum->name, "sum");
  ASSERT_EQ(sum->func_args.size(), 2u);
  EXPECT_EQ(sum->func_args[0].name, "x");
  EXPECT_EQ(sum->func_args[0].data_type.kind, DataTypeKind::kImplicit);
  EXPECT_EQ(sum->func_args[1].name, "y");
  EXPECT_EQ(sum->func_args[1].data_type.kind, DataTypeKind::kInt);

  // The clocking-block form and the block-item form, each reached only through
  // its own path.
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kClockingBlock), nullptr);
  auto* init = FindItemByKind(items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(init, nullptr);
  ASSERT_NE(init->body, nullptr);
  bool block_let_seen = false;
  for (auto* s : init->body->stmts) {
    if (s != nullptr && s->kind == StmtKind::kBlockItemDecl &&
        s->decl_item != nullptr &&
        s->decl_item->kind == ModuleItemKind::kLetDecl) {
      EXPECT_EQ(s->decl_item->name, "inner");
      block_let_seen = true;
    }
  }
  EXPECT_TRUE(block_let_seen);

  EXPECT_FALSE(ParseWithPreprocessorOk(InSv2005(kSrc)));
}

// The two remaining non-temporal additions, each of which lands as something
// the tree distinguishes. `restrict` opens a module item of its own kind,
// separate from the assert/assume/cover items the fourth included list already
// offers; `unique0` is a case qualifier of its own, distinct from the `unique`
// that list already has, and it qualifies the plain, the wildcard, and the
// conditional forms alike; and `global` turns a clocking block into the single
// one a design may have.
TEST(CompilerDirectiveParsing,
     SystemVerilog2009AddedQualifierWordsOpenConstructs) {
  const std::string kSrc =
      "module m (input logic clk, input logic req);\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] r;\n"
      "  global clocking gcb @(posedge clk); endclocking\n"
      "  restrict property (@(posedge clk) req);\n"
      "  initial begin\n"
      "    unique0 case (sel) 2'b01: r = 8'd1; default: r = 8'd0; endcase\n"
      "    unique0 casez (sel) 2'b1?: r = 8'd2; default: r = 8'd0; endcase\n"
      "    unique0 if (req) r = 8'd3; else r = 8'd4;\n"
      "  end\n"
      "endmodule\n";

  auto r = ParseWithPreprocessor(InSv2009(kSrc));
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto& items = r.cu->modules[0]->items;
  EXPECT_NE(FindItemByKind(items, ModuleItemKind::kRestrictProperty), nullptr);

  auto* clocking = FindItemByKind(items, ModuleItemKind::kClockingBlock);
  ASSERT_NE(clocking, nullptr);
  EXPECT_TRUE(clocking->is_global_clocking);
  EXPECT_FALSE(clocking->is_default_clocking);

  auto* init = FindItemByKind(items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(init, nullptr);
  ASSERT_NE(init->body, nullptr);
  size_t qualified = 0;
  for (auto* s : init->body->stmts) {
    if (s == nullptr) continue;
    if (s->kind == StmtKind::kCase || s->kind == StmtKind::kIf) {
      EXPECT_EQ(s->qualifier, CaseQualifier::kUnique0);
      ++qualified;
    }
  }
  EXPECT_EQ(qualified, 3u);

  EXPECT_FALSE(ParseWithPreprocessorOk(InSv2005(kSrc)));
}

// The bulk of Table 22-5 is temporal-property vocabulary, and its keyword role
// is to build a property expression. Each of the sixteen operators is written
// into a real property body under this version and the declaration is read back
// off the tree. The bodies themselves are written with `property`/`endproperty`
// and `assert property`, which come from the fourth included list -- the
// addition is only usable because of the inclusion.
//
// There is no paired rejection under "1800-2005" here, and there cannot be one:
// a property body is scanned to its closing keyword rather than parsed as an
// expression, so it admits any sequence of tokens under any reserved word list
// -- a body of pure punctuation is accepted too. The rejecting leg for these
// sixteen words is therefore carried by the identifier-slot sweep above, which
// is where reservation actually shows, and the version-sensitive half of the
// role is carried by the test below, which uses the five of them the parser
// really does read as operators.
TEST(CompilerDirectiveParsing,
     SystemVerilog2009AddedTemporalWordsBuildPropertyExpressions) {
  struct Operator {
    const char* word;
    const char* body;
  };
  const Operator kOperators[] = {
      {"eventually", "eventually [0:2] a"},
      {"s_eventually", "s_eventually a"},
      {"nexttime", "nexttime a"},
      {"s_nexttime", "s_nexttime a"},
      {"s_always", "s_always [0:1] a"},
      {"until", "a until b"},
      {"s_until", "a s_until b"},
      {"until_with", "a until_with b"},
      {"s_until_with", "a s_until_with b"},
      {"implies", "a implies b"},
      {"accept_on", "accept_on(b) a"},
      {"reject_on", "reject_on(b) a"},
      {"sync_accept_on", "sync_accept_on(b) a"},
      {"sync_reject_on", "sync_reject_on(b) a"},
      {"strong", "strong(##1 a)"},
      {"weak", "weak(##1 a)"},
  };
  EXPECT_EQ(std::size(kOperators), 16u);

  for (const auto& op : kOperators) {
    std::string src =
        std::string(
            "module m (input logic clk, input logic a, input logic b);\n"
            "  property p;\n"
            "    @(posedge clk) ") +
        op.body +
        ";\n"
        "  endproperty\n"
        "  assert property (p);\n"
        "endmodule\n";

    auto r = ParseWithPreprocessor(InSv2009(src));
    ASSERT_NE(r.cu, nullptr) << op.word;
    EXPECT_FALSE(r.has_errors) << op.word;
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kPropertyDecl, "p"))
        << op.word;
  }
}

// Reserving a temporal word is only half of it; the other half is that the word
// stands for a particular operator rather than for "some property word". Five
// of them carry an operand form the parser checks, and checking it is something
// only a keyword gets: a bracketed tick count shall not be negative, a range
// shall not run backwards, and an unbounded maximum is legal after the strong
// operator of a pair but not after the weak one. Each bad form is rejected here
// and accepted under "1800-2005", where the very same word is an ordinary
// identifier and so no operand rule attaches to it -- which is exactly the
// difference this version_specifier makes. The well-formed counterpart of each
// is accepted here too, so the rejections are the operand rule rather than the
// word being unusable, and three of those counterparts use a bracketed shape
// the sweep above does not reach.
//
// Every bound below is an integer literal, and deliberately so. The operand is
// a constant expression, so a parameter or a localparam may stand there too,
// but the parser checks only the literal form and leaves a symbolic bound to
// the stages that fold constants -- a parameter bound is accepted under this
// version and under the included lists alike, even in the mixed form where the
// other bound is the literal this rule rejects. Those forms therefore say
// nothing about which words are reserved, and belong to the subclause defining
// the operator rather than to this one. The constant forms are enumerated where
// they actually resolve: at the elaborator and at a run.
TEST(CompilerDirectiveParsing,
     SystemVerilog2009AddedTemporalWordsCarryTheirOwnOperandRules) {
  auto property_src = [](const char* body) {
    return std::string(
               "module m (input logic clk, input logic a);\n"
               "  property p;\n"
               "    @(posedge clk) ") +
           body +
           ";\n"
           "  endproperty\n"
           "  assert property (p);\n"
           "endmodule\n";
  };

  struct Form {
    const char* word;
    const char* bad;
    const char* good;
  };
  // The last two rows are the pair that differs only in strength, and they are
  // arranged so the table itself makes that comparison: the unbounded maximum
  // is the strong operator's well-formed operand and the weak one's bad
  // operand, the same source rejected on one row and accepted on the other.
  const Form kForms[] = {
      {"nexttime", "nexttime [-1] a", "nexttime [1] a"},
      {"s_nexttime", "s_nexttime [-1] a", "s_nexttime [1] a"},
      {"s_always", "s_always [1:$] a", "s_always [1:2] a"},
      {"eventually", "eventually [1:$] a", "eventually [1:2] a"},
      {"s_eventually", "s_eventually [3:1] a", "s_eventually [1:$] a"},
  };

  for (const auto& f : kForms) {
    EXPECT_FALSE(ParseWithPreprocessorOk(InSv2009(property_src(f.bad))))
        << f.word << " is read as an operator here, so its operand is checked";
    EXPECT_TRUE(ParseWithPreprocessorOk(InSv2009(property_src(f.good))))
        << f.word << " takes the well-formed operand";
    EXPECT_TRUE(ParseWithPreprocessorOk(InSv2005(property_src(f.bad))))
        << f.word << " is an ordinary identifier under the included lists";
  }
}

// Table 22-1 in its keyword role under this version: inclusion is not only
// about what a word may no longer name. The gate primitives build structure,
// the resolved net types and drive strengths are written out, and the
// procedural statements build control flow -- all under a region opened for
// this version_specifier.
TEST(CompilerDirectiveParsing,
     SystemVerilog2009IncludedVerilog1995WordsStillWork) {
  ExpectTable221ConstructsParse("1800-2009");
}

// Including Table 22-2 means including the ten words a configuration is written
// with, which is what separates it from the configuration-free companion list:
// seven of them appear here and the declaration is built. Under that companion
// list the very same source cannot be written, so the configuration exists here
// because this version inherits the full list.
TEST(CompilerDirectiveParsing, SystemVerilog2009IncludesTheConfigurationWords) {
  ExpectConfigurationWordsParse("1800-2009");
}

// The rest of Table 22-2 in its keyword role. `localparam` declares a constant,
// `genvar`/`generate`/`endgenerate` build a loop generate construct,
// `automatic` qualifies a subroutine, `signed` and `unsigned` qualify
// declarations, and the four pulse-control words are specify items -- each the
// construct its word exists to open, all still available under this version.
TEST(CompilerDirectiveParsing,
     SystemVerilog2009IncludedVerilog2001WordsStillWork) {
  ExpectTable222ConstructsParse("1800-2009");
}

// The fourth included list in its keyword role, which is the largest thing this
// version inherits: the data types, the user-defined types, the inferred
// processes, the design elements, and the verification vocabulary the added
// temporal words are written inside of. All of it still works under a region
// opened for this version_specifier.
TEST(CompilerDirectiveParsing,
     SystemVerilog2009IncludedSystemVerilog2005WordsStillWork) {
  ExpectTable224ConstructsParse("1800-2009");
}

// The negative the five tables imply, at the stage where it shows: a word none
// of them lists is an ordinary identifier under this version, so it names
// things freely and opens nothing. Both halves are here -- the same word naming
// a declaration and failing to be a data type -- because either one alone would
// leave the other unchecked. Each word is one the next standard reserves, so
// what is being bounded is this version's list and not the vocabulary at large.
TEST(CompilerDirectiveParsing, SystemVerilog2009LeavesLaterWordsAsIdentifiers) {
  // None of these opens a design element, so putting one at the head of a line
  // leaves the region machinery -- which tracks design elements by a line's
  // first word, without regard to the list in force -- out of the picture, and
  // the only thing that can reject the source is the word not being a type.
  const char* kLater[] = {"implements", "interconnect", "nettype", "soft"};
  for (const char* word : kLater) {
    auto r = ParseWithPreprocessor(InSv2009(VarDecl(word)));
    ASSERT_NE(r.cu, nullptr) << word;
    EXPECT_FALSE(r.has_errors) << word;
    ASSERT_EQ(r.cu->modules.size(), 1u) << word;
    EXPECT_TRUE(HasItemKindNamed(r.cu->modules[0]->items,
                                 ModuleItemKind::kVarDecl, word))
        << word;

    std::string as_type =
        std::string("module m;\n  ") + word + " [7:0] v;\nendmodule\n";
    EXPECT_FALSE(ParseWithPreprocessorOk(InSv2009(as_type)))
        << word << " is not a data type under this version";

    // The leg that makes each of these a *later* word rather than one this
    // implementation simply does not know: the specifier for the standard after
    // this one reserves it, so the very same declaration is refused there. That
    // is what places the boundary of this version's list between the two.
    EXPECT_FALSE(ParseWithPreprocessorOk(InSv2012(VarDecl(word))))
        << word << " is reserved by the version after this one";
  }
}

}  // namespace
