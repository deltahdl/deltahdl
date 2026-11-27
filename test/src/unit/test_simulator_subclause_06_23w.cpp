#include <gtest/gtest.h>

#include <array>
#include <format>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(MailboxOfTypeReferenceSim, CarriesAByte) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  mailbox #(type(byte)) m = new;\n"
                       "  byte b;\n"
                       "  initial begin\n"
                       "    m.put(8'd200);\n"
                       "    m.get(b);\n"
                       "    $display(\"%0d\", b);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "-56\n");
}

TEST(MailboxOfTypeReferenceSim, WeakReferenceOfAHandlesType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class K; int m = 5; endclass\n"
                       "module top;\n"
                       "  K k;\n"
                       "  weak_reference #(type(k)) w;\n"
                       "  initial begin\n"
                       "    k = new;\n"
                       "    w = new(k);\n"
                       "    $display(\"%0d\", w.get().m);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "5\n");
}

TEST(ScopeDeclarationTypeRefSim, PackageAndUnitVariablesTakeTheReferencedType) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package pk;\n"
                 "  logic [7:0] pb;\n"
                 "  int pa [4];\n"
                 "  var type(pb) pv;\n"
                 "  var type(pb[3:0]) ps;\n"
                 "  var type(pa) pf;\n"
                 "  function automatic int pbits();\n"
                 "    return $bits(pv);\n"
                 "  endfunction\n"
                 "  function automatic int psize();\n"
                 "    return $size(pf);\n"
                 "  endfunction\n"
                 "endpackage\n"
                 "logic [11:0] ub;\n"
                 "var type(ub) uv;\n"
                 "var type(ub + 4'b0) ue;\n"
                 "module top;\n"
                 "  logic [5:0] mb;\n"
                 "  var type(mb) mv;\n"
                 "  initial $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", "
                 "$bits(pk::pv), pk::pbits(), $bits(pk::ps), "
                 "pk::psize(), $bits(uv), $bits(ue), $isunknown(uv), "
                 "$bits(mv));\n"
                 "endmodule\n",
                 f),
      "8 8 4 4 12 12 1 6\n");
}

TEST(ScopeDeclarationTypeRefSim, ClassStaticPropertyGivesItsWholeType) {
  constexpr const char* kClasses =
      "class K; static int sq [$]; static int sa [3]; endclass\n"
      "class D; static byte sb; endclass\n"
      "class C #(int W = 1);\n"
      "  static byte sb;\n  static logic [W-1:0] sw;\nendclass\n";
  struct Place {
    const char* name;
    const char* before_module;
    const char* in_module;
  };
  constexpr std::array kPlaces = {
      Place{"classes in the compilation unit", kClasses, ""},
      Place{"classes in the module", "", kClasses},
  };
  for (const Place& place : kPlaces) {
    SCOPED_TRACE(place.name);
    const std::string kSrc = std::format(
        "package q;\n  class D; static byte sb; endclass\nendpackage\n"
        "{}"
        "module top;\n"
        "{}"
        "  int mq [$];\n  int ma [3];\n  byte mb;\n"
        "  typedef type(K::sq) TK;\n  typedef type(mq) TM;\n"
        "  TK tk;\n  TM tm;\n"
        "  var type(K::sa) ka;\n  var type(ma) mf;\n"
        "  var type(D::sb) a;\n  var type(q::D::sb) b;\n"
        "  var type(C#(1)::sb) c;\n  var type(C#(5)::sw) w;\n"
        "  var type(mb) d;\n"
        "  initial begin\n"
        "    tk.push_back(1);\n    tk.push_back(2);\n    tm.push_back(1);\n"
        "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d %0d\", tk.size(), "
        "tm.size(), $size(ka), $size(mf), $bits(a), $bits(b), $bits(c), "
        "$bits(w), $bits(d));\n"
        "  end\n"
        "endmodule\n",
        place.before_module, place.in_module);
    SCOPED_TRACE(kSrc);
    SimFixture f;
    EXPECT_EQ(RunCapture(kSrc, f), "2 1 3 3 8 8 8 5 8\n");
  }
}

}  // namespace
