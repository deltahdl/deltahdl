#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_fsm_pragma_lexing.h"
#include "lexer/lexer.h"

using namespace delta;

// §40.4.5 — Specifying current and next state signals in same declaration.
//
// When the enumeration-name pragma (§40.4.1's separate `/* tool enum E */`
// form) is written inside a declaration that declares several signals, the tool
// assumes a positional convention: the first signal following the pragma holds
// the current state, the second signal holds the next state, and nothing is
// assumed about any further signal. The LRM's example is:
//
//     /* tool state_vector cs */
//     logic [1:0] /* tool enum myFSM */ cs, ns, nonstate;
//
// Here cs is the current state, ns is the next state, and nonstate is ignored.
//
// Lexically nothing new happens: §40.4.1 already records the `state_vector`
// pragma and the enum-only pragma context-independently, and every declared
// signal name reaches the token stream in declaration order. The positional
// current/next/ignored assignment is a semantic FSM-extraction interpretation
// layered on top of those tokens — the same kind of semantic decision §40.4.4
// noted the lexer does not make. These tests observe that the existing
// recognition surfaces exactly the material a downstream extractor needs to
// apply §40.4.5's rule, and that the lexer singles out no trailing signal.

namespace {

// Shared setup: the §40.4.5 declarations all carry a `state_vector cs` pragma
// followed by an `enum myFSM` pragma. Asserts that exact two-pragma shape.
void ExpectCsThenMyFsmPragmas(const std::vector<FsmPragmaInfo>& pragmas) {
  ASSERT_EQ(pragmas.size(), 2u);
  EXPECT_EQ(pragmas[0].form, "state_vector");
  EXPECT_EQ(pragmas[0].signal, "cs");
  EXPECT_FALSE(pragmas[0].has_enum);
  EXPECT_EQ(pragmas[1].form, "enum_only");
  EXPECT_TRUE(pragmas[1].has_enum);
  EXPECT_EQ(pragmas[1].enum_name, "myFSM");
}

// Exactly one pragma binds a signal name (cs); the enum-only pragma leaves it
// empty, so no lexer output ties any trailing signal to the FSM.
void ExpectOnlyCsIsSignalBearing(const std::vector<FsmPragmaInfo>& pragmas) {
  int signal_bearing = 0;
  for (const auto& p : pragmas) {
    if (!p.signal.empty()) {
      ++signal_bearing;
      EXPECT_EQ(p.signal, "cs");
    }
  }
  EXPECT_EQ(signal_bearing, 1);
}

// Collects the identifiers from `src` that belong to `names`, in declaration
// order, so a test can assert which signal is current/next and which trail.
std::vector<std::string> CollectDeclOrder(
    const std::string& src, const std::vector<std::string>& names) {
  auto idents = CollectIdentifiers(src);
  std::vector<std::string> decl_order;
  for (const auto& id : idents) {
    for (const auto& want : names) {
      if (id == want) {
        decl_order.push_back(id);
        break;
      }
    }
  }
  return decl_order;
}

// R1 + R2: the §40.4.5 example. The state_vector pragma names cs and the
// enum-only pragma binds the FSM enumeration myFSM; both are recognized for the
// multi-signal declaration. Every declared signal — cs, ns, nonstate — reaches
// the token stream in declaration order, which is precisely what a downstream
// extractor consumes to assign the first following signal (cs) the current
// state and the second (ns) the next state.
TEST(FsmSameDeclarationPragmaLexing,
     RecognizesCurrentAndNextStateSignalsInSameDeclaration) {
  const std::string src =
      "module fsm;\n"
      "  /* tool state_vector cs */\n"
      "  logic [1:0] /* tool enum myFSM */ cs, ns, nonstate;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(src);
  ExpectCsThenMyFsmPragmas(pragmas);

  // The pragmas are comments: all three declared signals still lex, and they
  // appear in declaration order. The first following the enum pragma is the
  // current state (cs) and the next is the next state (ns).
  auto decl_order = CollectDeclOrder(src, {"cs", "ns", "nonstate"});
  ASSERT_EQ(decl_order.size(), 3u);
  EXPECT_EQ(decl_order[0], "cs");
  EXPECT_EQ(decl_order[1], "ns");
  EXPECT_EQ(decl_order[2], "nonstate");
}

// R3: nothing is assumed about the trailing signal. The lexer records no pragma
// that names ns or nonstate as a signal — the only signal-bearing pragma is the
// state_vector naming cs, and the enum-only pragma carries no signal name at
// all. The positional/ignored interpretation is left entirely to downstream
// FSM extraction; the lexer singles out no trailing signal of its own.
TEST(FsmSameDeclarationPragmaLexing, NothingIsAssumedAboutAdditionalSignals) {
  const std::string src =
      "module fsm;\n"
      "  /* tool state_vector cs */\n"
      "  logic [1:0] /* tool enum myFSM */ cs, ns, nonstate;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(src);
  for (const auto& p : pragmas) {
    EXPECT_NE(p.signal, "ns");
    EXPECT_NE(p.signal, "nonstate");
  }

  // Exactly one pragma binds a signal name (cs); the enum-only pragma leaves it
  // empty, so no lexer output ties ns or nonstate to the FSM.
  ExpectOnlyCsIsSignalBearing(pragmas);
}

// R1 + R2 at the minimal "declaration of multiple signals": exactly two
// signals. The state_vector pragma names cs and the enum-only pragma binds the
// FSM enumeration. With only cs and ns declared, the first following signal
// (cs) is the current state and the second (ns) is the next state — there is no
// trailing signal for the ignore rule to act on. The lexer still records one
// signal-bearing pragma (cs) and surfaces both names in declaration order.
TEST(FsmSameDeclarationPragmaLexing,
     TwoSignalDeclarationAssignsCurrentThenNextState) {
  const std::string src =
      "module fsm;\n"
      "  /* tool state_vector cs */\n"
      "  logic [1:0] /* tool enum myFSM */ cs, ns;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(src);
  ExpectCsThenMyFsmPragmas(pragmas);

  auto decl_order = CollectDeclOrder(src, {"cs", "ns"});
  ASSERT_EQ(decl_order.size(), 2u);
  EXPECT_EQ(decl_order[0], "cs");  // current state
  EXPECT_EQ(decl_order[1], "ns");  // next state

  ExpectOnlyCsIsSignalBearing(pragmas);
}

// R3 generalized beyond the single `nonstate` of the LRM example: when more
// than one signal trails the current/next pair, nothing is assumed about ANY of
// them. cs holds the current state and ns the next state; both idle and extra
// are trailing signals the lexer must not tie to the FSM. The lexer records a
// single signal-bearing pragma (cs) and surfaces every declared signal in
// order, leaving all trailing signals for downstream extraction to ignore.
TEST(FsmSameDeclarationPragmaLexing, MultipleTrailingSignalsAreAllIgnored) {
  const std::string src =
      "module fsm;\n"
      "  /* tool state_vector cs */\n"
      "  logic [1:0] /* tool enum myFSM */ cs, ns, idle, extra;\n"
      "endmodule\n";

  auto pragmas = CollectFsmPragmas(src);
  for (const auto& p : pragmas) {
    EXPECT_NE(p.signal, "ns");
    EXPECT_NE(p.signal, "idle");
    EXPECT_NE(p.signal, "extra");
  }

  ExpectOnlyCsIsSignalBearing(pragmas);

  auto decl_order = CollectDeclOrder(src, {"cs", "ns", "idle", "extra"});
  ASSERT_EQ(decl_order.size(), 4u);
  EXPECT_EQ(decl_order[0], "cs");     // current state
  EXPECT_EQ(decl_order[1], "ns");     // next state
  EXPECT_EQ(decl_order[2], "idle");   // ignored
  EXPECT_EQ(decl_order[3], "extra");  // ignored
}

}  // namespace
