#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kEventFormalReferenced =
    "event formal 'e' of a let is referenced where no event_expression may be "
    "written";
constexpr std::string_view kChandleFormal =
    "let formal argument 'c' must be of type event or a type allowed in a "
    "Boolean expression";

TEST(LetDeclElaboration, FormalsOfABlocksLetAreChecked) {
  ElabFixture f;
  ElaborateSrc(
      "function automatic int cf();\n"
      "  let a(event e) = e + 1;\n"
      "  return 0;\n"
      "endfunction\n"
      "package p;\n"
      "  class K;\n"
      "    function int km();\n"
      "      let b(event e) = e + 1;\n"
      "      return 0;\n"
      "    endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m;\n"
      "  initial begin\n"
      "    let f(event e) = e + 1;\n"
      "    let g(chandle c) = 1;\n"
      "    let ok(x, event e) = $rose(x, @(e));\n"
      "  end\n"
      "  initial fork\n"
      "    let h(event e) = e + 1;\n"
      "  join\n"
      "  function automatic int mf();\n"
      "    let k(event e) = e + 1;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  class C;\n"
      "    function int cm();\n"
      "      let n(event e) = e + 1;\n"
      "      return 0;\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  for (uint32_t line : {2u, 8u, 15u, 20u, 23u, 28u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kEventFormalReferenced,
                              line, "11.12"));
  }
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kChandleFormal, 16, "11.12"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "event formal", 17, "11.12"));
}

TEST(LetDeclElaboration, FormalsOfAPackagesLetAreChecked) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  let f(event e) = e + 1;\n"
      "  let g(chandle c) = 1;\n"
      "  let ok(x, event e) = $rose(x, @(e));\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kEventFormalReferenced, 2, "11.12"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kChandleFormal, 3, "11.12"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "event formal", 4, "11.12"));
}

TEST(LetDeclElaboration, CallsToABlocksLetAreChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [2]; int i;\n"
      "  let f(x) = x;\n"
      "  initial begin\n"
      "    let f(int x) = x;\n"
      "    let d(int x = arr) = x;\n"
      "    $display(\"%0d\", f(arr));\n"
      "    begin\n"
      "      $display(\"%0d\", f(arr));\n"
      "    end\n"
      "  end\n"
      "  initial $display(\"%0d\", f(arr) + f(i));\n"
      "  function automatic int fn();\n"
      "    let g(int x) = x;\n"
      "    return g(arr);\n"
      "  endfunction\n"
      "  initial fork\n"
      "    let h(int x) = x;\n"
      "    $display(\"%0d\", h(arr));\n"
      "  join\n"
      "endmodule\n",
      f);
  for (uint32_t line : {6u, 7u, 9u, 15u, 19u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "'arr' is not cast compatible with the type of "
                              "formal 'x'",
                              line, "11.12"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "is not cast compatible with the type of formal",
                             12, "11.12"));
}

TEST(LetDeclElaboration, CallsToACompilationUnitsLetAreChecked) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct { int a; byte b; } s_t;\n"
      "typedef int arr_t [3];\n"
      "s_t s;\n"
      "let f(int x) = x;\n"
      "let d(int x, y = s) = x;\n"
      "let p(arr_t x) = x[0];\n"
      "let g(int x) = x;\n"
      "function automatic int c(); return f(s); endfunction\n"
      "module m;\n"
      "  int arr [2]; int i; arr_t w;\n"
      "  function automatic int g(int v); return v; endfunction\n"
      "  initial begin\n"
      "    $display(\"%0d\", f(arr));\n"
      "    $display(\"%0d\", f(s));\n"
      "    $display(\"%0d\", f(i) + p(w) + g(arr));\n"
      "    $display(\"%0d\", p(arr));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'s' is not cast compatible with the type of "
                            "formal 'y'",
                            5, "11.12"));
  EXPECT_EQ(std::ranges::count_if(f.diag.Diagnostics(),
                                  [](const Diagnostic& d) {
                                    return d.loc.line == 5 &&
                                           d.message.find("not cast") !=
                                               std::string::npos;
                                  }),
            1);
  for (uint32_t line : {8u, 13u, 14u, 16u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "is not cast compatible with the type of formal "
                              "'x'",
                              line, "11.12"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "is not cast compatible with the type of formal",
                             15, "11.12"));
}

TEST(LetDeclElaboration, CallsToAPackagesLetAreChecked) {
  ElabFixture f;
  ElaborateSrc(
      "function automatic int uf(int v); return v; endfunction\n"
      "package p;\n"
      "  typedef int t;\n"
      "  typedef int a_t [2];\n"
      "  let f(int x) = x;\n"
      "  let g(t x) = x;\n"
      "  let h(a_t x) = x[0];\n"
      "  function automatic int pf(int v); return v; endfunction\n"
      "endpackage\n"
      "package q;\n"
      "  let k(int x) = x;\n"
      "endpackage\n"
      "module m;\n"
      "  import p::*;\n"
      "  import q::k;\n"
      "  class C; static function int sf(int v); return v; endfunction"
      " endclass\n"
      "  int arr [2]; int i;\n"
      "  initial begin\n"
      "    $display(\"%0d\", p::f(arr));\n"
      "    $display(\"%0d\", f(arr));\n"
      "    $display(\"%0d\", k(arr));\n"
      "    $display(\"%0d\", p::g(arr));\n"
      "    $display(\"%0d\", p::h(i));\n"
      "    $display(\"%0d\", p::g(i) + g(i) + p::h(arr) + h(arr));\n"
      "    $display(\"%0d\", p::pf(i) + C::sf(i) + uf(i));\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {19u, 20u, 21u, 22u, 23u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "is not cast compatible with the type of formal "
                              "'x'",
                              line, "11.12"));
  }
  for (uint32_t line : {24u, 25u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "is not cast compatible with the type of formal",
                               line, "11.12"));
  }
}

TEST(LetDeclElaboration, ACompilationUnitLetsTypeReferenceFormalIsResolved) {
  ElabFixture f;
  ElaborateSrc(
      "chandle ch;\n"
      "byte b;\n"
      "let f(type(ch) c) = 1;\n"
      "let g(type(b) y) = y;\n"
      "module m;\n"
      "  int arr [2];\n"
      "  initial $display(\"%0d\", g(arr));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kChandleFormal, 3, "11.12"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'arr' is not cast compatible with the type of "
                            "formal 'y'",
                            7, "11.12"));
}

TEST(LetElaboration, AScopedCallIsNoHierarchicalReference) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  let f(x) = x;\n"
      "endpackage\n"
      "module child;\n"
      "  let f(x) = !x;\n"
      "endmodule\n"
      "module m;\n"
      "  let f(x) = x + 1;\n"
      "  class C; static function int f(int v); return v; endfunction"
      " endclass\n"
      "  child u();\n"
      "  initial $display(\"%0d\", p::f(1) + C::f(1));\n"
      "  initial $display(\"%0d\", u.f(1'b0));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "a let shall not be referenced hierarchically", 11,
                             "11.12"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a let shall not be referenced hierarchically", 12,
                            "11.12"));
}

}  // namespace
