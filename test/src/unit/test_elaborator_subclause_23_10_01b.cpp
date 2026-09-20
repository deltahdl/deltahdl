#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

// Parameter `name` of module `mod` once `src` is elaborated under top, or -1
// where the source does not elaborate, the module declares no such parameter
// or the fold left it unresolved: no case expects -1 of a parameter it reads.
int64_t ParamOfModule(const std::string& src, std::string_view mod,
                      std::string_view name, ElabFixture& f) {
  auto* design = ElaborateSrc(src, f, "top");
  if (design == nullptr) return -1;
  const auto* p = FindParam(design, mod, name);
  return p != nullptr && p->is_resolved ? p->resolved_value : -1;
}

// A module `name` declaring `parameter int TOP = 15`, a typedef `vec_t` of
// `logic [range]` and `parameter vec_t P = 0`, with B reading $bits(P).
std::string TypedefRangedModule(std::string_view name, std::string_view range) {
  std::string src = "module ";
  src += name;
  src +=
      ";\n"
      "  parameter int TOP = 15;\n"
      "  typedef logic [";
  src += range;
  src +=
      "] vec_t;\n"
      "  parameter vec_t P = 0;\n"
      "  localparam int B = $bits(P);\n"
      "endmodule\n";
  return src;
}

// §23.9 (printed page 761) makes a module a scope of its own and §6.18
// (printed 118) has a typedef name stand for the declaration of the scope it
// is written in, so two modules each declaring a `vec_t` of their own size
// their `parameter vec_t P` by their own typedef when a defparam makes TOP
// over: a's `logic [TOP:0]` under `defparam ua.TOP = 7` is 8 bits and b's
// `logic [TOP*4+3:0]` under `defparam ub.TOP = 3` is 16. Sized by the other
// module's typedef, a's P would read 32 bits and b's 4. The table the resize
// reads lays the module's own typedef items over the design-wide union
// (ModuleTypedefTable in src/elaborator/elaborator_defparam.cpp), which is
// what this pins.
TEST(DefparamElaboration, SizesEachModulesTypedefParameterByItsOwnTypedef) {
  const std::string kSrc = TypedefRangedModule("a", "TOP:0") +
                           TypedefRangedModule("b", "TOP*4+3:0") +
                           "module top;\n"
                           "  a ua();\n"
                           "  b ub();\n"
                           "  defparam ua.TOP = 7;\n"
                           "  defparam ub.TOP = 3;\n"
                           "endmodule\n";
  ElabFixture fa;
  EXPECT_EQ(ParamOfModule(kSrc, "a", "B", fa), 8);
  EXPECT_FALSE(fa.has_errors);
  ElabFixture fb;
  EXPECT_EQ(ParamOfModule(kSrc, "b", "B", fb), 16);
}

// §27.4 (printed page 820) has a generate block's declarations in scope for
// its items and §6.18 (printed 118) makes a typedef name stand for that
// declaration, so g's `parameter vec_t P` under g's own `typedef logic
// [TOP:0] vec_t` follows the module's TOP, which §23.10.1 (printed 764-765)
// lets `defparam u.TOP = 7` change: $bits(P) is 8, the module-level `typedef
// logic [3:0] vec_t` notwithstanding. The elaborator applies the defparam
// before it elaborates g (Elaborator::ResolveDefparamsAndGenerates), so g is
// sized with TOP at 7 and nothing is sized over again; this pins that order.
// The defparam's early resolution was verified again after the block's
// declarations had grown m's parameter vector, by the address the target
// had before, and reported §23.10.4.2 on a name that resolved the same.
TEST(DefparamElaboration, ResizesAGenerateBlocksParameterByTheBlocksTypedef) {
  ElabFixture f;
  EXPECT_EQ(ParamOfModule("module m;\n"
                          "  parameter int TOP = 15;\n"
                          "  typedef logic [3:0] vec_t;\n"
                          "  if (1) begin : g\n"
                          "    typedef logic [TOP:0] vec_t;\n"
                          "    parameter vec_t P = 0;\n"
                          "    localparam int B = $bits(P);\n"
                          "  end\n"
                          "endmodule\n"
                          "module top;\n"
                          "  m u();\n"
                          "  defparam u.TOP = 7;\n"
                          "endmodule\n",
                          "m", "B", f),
            8);
  EXPECT_FALSE(f.has_errors);
}

// §27.5 (printed page 824) instantiates at most one alternative of a
// conditional generate construct into the model and lets the alternatives
// share a name, so the g elaborated is the one declaring `typedef logic
// [TOP:0] vec_t`, and its P is 8 bits under `defparam u.TOP = 7`, the else's
// `logic [3:0] vec_t` reaching nothing.
TEST(DefparamElaboration, SizesByTheSelectedAlternativesTypedefAlone) {
  ElabFixture f;
  EXPECT_EQ(ParamOfModule("module m;\n"
                          "  parameter int TOP = 15;\n"
                          "  if (1) begin : g\n"
                          "    typedef logic [TOP:0] vec_t;\n"
                          "    parameter vec_t P = 0;\n"
                          "    localparam int B = $bits(P);\n"
                          "  end else begin : g\n"
                          "    typedef logic [3:0] vec_t;\n"
                          "  end\n"
                          "endmodule\n"
                          "module top;\n"
                          "  m u();\n"
                          "  defparam u.TOP = 7;\n"
                          "endmodule\n",
                          "m", "B", f),
            8);
  EXPECT_FALSE(f.has_errors);
}

// Parameter `name` of module m declared in the generate block instance
// `prefix` names, as RtlirParamDecl::gen_block_prefix spells it, or -1.
int64_t BlockParamOfM(RtlirDesign* design, std::string_view prefix,
                      std::string_view name) {
  const auto* m = FindModule(design, "m");
  if (m == nullptr) return -1;
  for (const auto& p : m->params) {
    if (p.name == name && p.gen_block_prefix == prefix) return p.resolved_value;
  }
  return -1;
}

// §27.4 (printed page 820) indexes a loop generate block's instances by the
// genvar's value, each a scope of its own with the typedef its body declares,
// so the second instance's P is sized by its own vec_t under `defparam
// u.TOP = 7` as the first's is: g[1]'s B reads 8, read by the `g_1_` prefix
// its declaration is keyed under.
TEST(DefparamElaboration, SizesEachLoopInstancesParameterByItsOwnTypedef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int TOP = 15;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    typedef logic [TOP:0] vec_t;\n"
      "    parameter vec_t P = 0;\n"
      "    localparam int B = $bits(P);\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  m u();\n"
      "  defparam u.TOP = 7;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(BlockParamOfM(design, "g_1_", "B"), 8);
  EXPECT_EQ(BlockParamOfM(design, "g_0_", "B"), 8);
  EXPECT_FALSE(f.has_errors);
}

// A module c whose `logic [W-1:0] P` follows `parameter int W = 32`, with H
// reading P's word above bit 64 and M its bits 47 down to 32.
constexpr std::string_view kWideningC =
    "module c;\n"
    "  parameter int W = 32;\n"
    "  parameter logic [W-1:0] P = 0;\n"
    "  localparam int H = P[95:64], M = P[47:32];\n"
    "endmodule\n";

// c's parameter `name` under a top holding `top_items`.
int64_t WideParamOfC(std::string_view top_items, std::string_view name,
                     ElabFixture& f) {
  std::string src(kWideningC);
  src += "module top;\n";
  src += top_items;
  src += "endmodule\n";
  return ParamOfModule(src, "c", name, f);
}

// Under `top_items`, c's P holds 96'h1_0000_0003_0000_0005 in full: H reads
// 1 and M 3, with nothing reported.
void ExpectEveryWordOfP(std::string_view top_items) {
  ElabFixture fh;
  EXPECT_EQ(WideParamOfC(top_items, "H", fh), 1);
  EXPECT_FALSE(fh.has_errors);
  ElabFixture fm;
  EXPECT_EQ(WideParamOfC(top_items, "M", fm), 3);
}

// §27.4 (printed page 820) and §23.9 (printed 761) have a generate block's
// declarations in scope for the items written in it, and §23.10.1 (printed
// 764-765) folds a defparam's right-hand side where the statement stands, so
// `defparam u.P = V` in block g reads g's 96-bit localparam V, and `defparam
// u.W = 96` after it, converting P's value over again to the 96 bits it now
// has (§6.20.2, printed 126), reads every word of V: H is 1 and M is 3. The
// refold registered the module holding the statement and no block, under
// which V's declaration was out of sight and its word above bit 64 read 0;
// and c, elaborated inside g, had W, P, H and M keyed under g's prefix, so
// that the fold making them over after `defparam u.W = 96`, standing in no
// block, saw none of them and left H and M at 0.
TEST(DefparamElaboration, RefoldsAGenerateBlocksDefparamValueWithItsNames) {
  constexpr std::string_view kTop =
      "  if (1) begin : g\n"
      "    localparam logic [95:0] V = 96'h1_0000_0003_0000_0005;\n"
      "    c u();\n"
      "    defparam u.P = V;\n"
      "    defparam u.W = 96;\n"
      "  end\n";
  ExpectEveryWordOfP(kTop);
}

// §23.10.2 (printed page 766) assigns an instance's parameter value to the
// parameter and §6.20.2 (printed 126) converts it to the range the
// declaration finally has, so `c #(.P(96'h1_0000_0003_0000_0005)) u()` with
// `defparam u.W = 96` after it gives P every digit of the literal: M reads
// the 3 at bits 47 down to 32 and H the 1 above bit 64. The value was
// converted from the 5 the 32-bit range had kept of it, so M read 0.
TEST(DefparamElaboration, RefoldsAnInstanceOverrideALaterDefparamWidens) {
  constexpr std::string_view kTop =
      "  c #(.P(96'h1_0000_0003_0000_0005)) u();\n"
      "  defparam u.W = 96;\n";
  ExpectEveryWordOfP(kTop);
}

// The same with the override written as the instantiating module's own
// 96-bit localparam, `.P(PP)`, whose words above bit 64 are read under top's
// registration alone: the refold stands in the scope the instantiation was
// written in, so H reads 1 and M 3 as for the literal.
TEST(DefparamElaboration, RefoldsAnInstanceOverrideNamingTheParentsParameter) {
  constexpr std::string_view kTop =
      "  localparam logic [95:0] PP = 96'h1_0000_0003_0000_0005;\n"
      "  c #(.P(PP)) u();\n"
      "  defparam u.W = 96;\n";
  ExpectEveryWordOfP(kTop);
}

// Both values given in the instantiation, `c #(.W(96), .P(...))`: W is 96
// before P is sized, so P is converted once, to 96 bits, and reads the same
// H and M with no defparam involved.
TEST(DefparamElaboration, WidensAnInstanceOverrideGivenInThePortList) {
  constexpr std::string_view kTop =
      "  c #(.W(96), .P(96'h1_0000_0003_0000_0005)) u();\n";
  ExpectEveryWordOfP(kTop);
}

// Whether the §23.10.1 report a defparam reaching outside its generate block
// gets was made at `line`.
::testing::AssertionResult EscapeReportedAt(const ElabFixture& f,
                                            uint32_t line) {
  return ReportedError(f.diag.Diagnostics(),
                       "defparam in a generate block shall not change a "
                       "parameter value outside that block",
                       line, "23.10.1");
}

// §23.10.1 (printed page 764) forbids a defparam statement in a hierarchy in
// or under a generate block instance from changing a parameter value outside
// that hierarchy, and §23.8 lets a module-level statement name its target
// from a top-level module: `module w; defparam top.u2.P = 5, top.Q = 6;`
// with w instantiated inside top's block g reaches c's P and top's own Q
// outside g and is refused as a statement written in the block is, P and Q
// keeping their declarations' 1. The top-rooted reading was gated on the
// statement's own position in its module alone, so w's instance standing
// under g went unnoticed and P read 5.
TEST(DefparamElaboration, ModuleUnderAGenerateBlockCannotEscapeIt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c;\n"
      "  parameter int P = 1;\n"
      "endmodule\n"
      "module w;\n"
      "  defparam top.u2.P = 5;\n"
      "  defparam top.Q = 6;\n"
      "endmodule\n"
      "module top;\n"
      "  parameter int Q = 1;\n"
      "  c u2();\n"
      "  if (1) begin : g\n"
      "    w u();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  const auto* p = FindParam(design, "c", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->resolved_value, 1);
  const auto* q = FindParam(design, "top", "Q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->resolved_value, 1);
  EXPECT_TRUE(EscapeReportedAt(f, 5));
  EXPECT_TRUE(EscapeReportedAt(f, 6));
}

// The block instance a module stands under is the innermost one on the way
// down to it, whichever module holds it, and a module instantiated at the
// module level of one under a block stands under that block too: x, held by
// w, held by mid's block g, held by top, names top's u2 outside g and is
// refused, the walk from top passing u2 without ever leaving mid into g.
TEST(DefparamElaboration, ModuleUnderANestedGenerateBlockCannotEscapeIt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c;\n"
      "  parameter int P = 1;\n"
      "endmodule\n"
      "module x;\n"
      "  defparam top.u2.P = 5;\n"
      "endmodule\n"
      "module w;\n"
      "  x v();\n"
      "endmodule\n"
      "module mid;\n"
      "  if (1) begin : g\n"
      "    w u();\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  c u2();\n"
      "  mid m();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  const auto* p = FindParam(design, "c", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->resolved_value, 1);
  EXPECT_TRUE(EscapeReportedAt(f, 5));
}

// The same statement naming a parameter inside the block that holds w's
// instance, `defparam top.g.u3.P = 5` on the sibling instance u3, changes
// nothing outside that hierarchy and is applied: P reads 5 with nothing
// reported.
TEST(DefparamElaboration, ModuleUnderAGenerateBlockReachesItsSibling) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c;\n"
      "  parameter int P = 1;\n"
      "endmodule\n"
      "module w;\n"
      "  defparam top.g.u3.P = 5;\n"
      "endmodule\n"
      "module top;\n"
      "  if (1) begin : g\n"
      "    c u3();\n"
      "    w u();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  const auto* p = FindParam(design, "c", "P");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(p->resolved_value, 5);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
