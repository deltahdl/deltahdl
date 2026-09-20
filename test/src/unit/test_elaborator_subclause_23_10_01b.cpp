#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
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
// which V's declaration was out of sight and its word above bit 64 read 0.
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

}  // namespace
