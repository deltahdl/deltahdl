#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kNotOnHandles =
    "operator is not allowed on class object handles";

constexpr uint32_t kFirstStatementLine = 8;

std::string HandleOperandsIn(std::initializer_list<std::string_view> stmts) {
  std::string src(
      "class C; endclass\nmodule t;\n  C h, g;\n  int r;\n  logic x;\n"
      "  logic [63:0] v;\n  initial begin\n");
  for (auto stmt : stmts) src.append("    ").append(stmt).append("\n");
  return src.append("  end\nendmodule\n");
}

void ExpectEachLineReported(std::initializer_list<std::string_view> stmts) {
  ElabFixture f;
  ElaborateSrc(HandleOperandsIn(stmts), f);
  uint32_t line = kFirstStatementLine;
  for (auto stmt : stmts) {
    SCOPED_TRACE(stmt);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotOnHandles, line++, "8.4"));
  }
}

TEST(ClassObjectElaboration, EveryUnaryOperatorOnAHandleIsReported) {
  ExpectEachLineReported({"r = -h;", "r = +h;", "r = ~h;", "r = !h;", "r = &h;",
                          "r = ~&h;", "r = |h;", "r = ~|h;", "r = ^h;",
                          "r = ~^h;", "r = ^~h;", "++h;", "--h;", "h++;",
                          "h--;"});
}

TEST(ClassObjectElaboration, EveryBinaryOperatorOutsideTheListIsReported) {
  ExpectEachLineReported(
      {"r = h + 1;",  "r = 1 - h;",   "r = h * 2;",   "r = h / 2;",
       "r = h ** 2;", "r = h % 2;",   "r = h & 1;",   "r = h | 1;",
       "r = h ^ 1;",  "r = h ~^ 1;",  "r = h ^~ 1;",  "r = h << 1;",
       "r = h >> 1;", "r = h <<< 1;", "r = h >>> 1;", "r = h && x;",
       "r = x || h;", "r = h -> x;",  "r = h <-> x;", "r = h < g;",
       "r = h <= g;", "r = h > g;",   "r = h >= g;"});
}

TEST(ClassObjectElaboration, EveryCompoundAssignmentToAHandleIsReported) {
  ExpectEachLineReported({"h += 1;", "h -= 1;", "h *= 2;", "h /= 2;", "h %= 2;",
                          "h &= 1;", "h |= 1;", "h ^= 1;", "h <<= 1;",
                          "h >>= 1;", "h <<<= 1;", "h >>>= 1;"});
}

TEST(ClassObjectElaboration,
     DISABLED_AHandleInAConcatenationOrReplicationIsReported) {
  ExpectEachLineReported({"v = {h};", "v = {h, g};", "v = {2{h}};"});
}

TEST(ClassObjectElaboration, TheOperatorsListedForHandlesAreAccepted) {
  EXPECT_TRUE(ElabOk(HandleOperandsIn(
      {"r = h == g;", "r = h != null;", "r = null == h;", "r = h === g;",
       "r = h !== null;", "h = x ? h : g;", "h = x ? null : h;",
       "r = (h == null) ? 1 : 0;", "h = g;", "h = null;", "h = new;"})));
}

constexpr std::string_view kHandleOperatorsInOtherPlaces =
    "class C; endclass\n"
    "package k;\n"
    "  C h; int r;\n"
    "  function void f(); r = h + 1; endfunction\n"
    "  function void f2(); r = h == null; endfunction\n"
    "endpackage\n"
    "C uh; int ur;\n"
    "function void uf(); ur = !uh; endfunction\n"
    "function void uf2(); ur = uh != null; endfunction\n"
    "interface i;\n"
    "  C h; int r;\n"
    "  initial r = h * 2;\n"
    "  initial r = h === null;\n"
    "endinterface\n"
    "program p;\n"
    "  C h; int r;\n"
    "  initial r = h << 1;\n"
    "  initial r = h !== null;\n"
    "endprogram\n"
    "module t;\n"
    "  C h; int r;\n"
    "  i ui();\n"
    "  p up();\n"
    "  if (1) begin : gb\n"
    "    initial r = h & 1;\n"
    "    initial r = h != null;\n"
    "  end\n"
    "endmodule\n";

TEST(ClassObjectElaboration,
     AnOperatorOnAHandleInAnInterfaceOrProgramIsReported) {
  ElabFixture f;
  ElaborateSrc(std::string(kHandleOperatorsInOtherPlaces), f);
  for (const uint32_t kLine : {12u, 17u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotOnHandles, kLine, "8.4"))
        << kLine;
  }
  for (const uint32_t kLine : {5u, 9u, 13u, 18u, 26u}) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kNotOnHandles, kLine, "8.4"))
        << kLine;
  }
}

TEST(ClassObjectElaboration,
     DISABLED_AnOperatorOnAHandleInAPackageUnitOrGenerateBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(std::string(kHandleOperatorsInOtherPlaces), f);
  for (const uint32_t kLine : {4u, 8u, 25u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotOnHandles, kLine, "8.4"))
        << kLine;
  }
}

}  // namespace
