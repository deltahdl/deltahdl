#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

// §8.23: from outside a class, `::` reaches its static properties and methods,
// its parameters and its types. A property or method written without `static`
// belongs to an object, which `C::x` and `C::f()` in a module name none of, so
// each is an error, while a static member and a parameter stay reachable.
TEST(ClassScopeResolutionElaboration, ANonStaticMemberIsNotReachedFromOutside) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  parameter int P = 3;\n"
      "  int x = 5;\n"
      "  static int s = 7;\n"
      "  function int f(); return 1; endfunction\n"
      "  static function int g(); return 2; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int y;\n"
      "  initial begin\n"
      "    y = C::x;\n"
      "    y = C::f();\n"
      "    y = C::s + C::g() + C::P;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (auto [line, member] :
       std::initializer_list<std::pair<uint32_t, const char*>>{{11u, "x"},
                                                               {12u, "f"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("cannot reach non-static member '") +
                                  member +
                                  "' through the class scope operator from "
                                  "outside its class",
                              line, "8.23"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

// §8.8's typed constructor call names the constructor through `::` with no
// object, `D::new(4)` building a D for a C handle, so `new` is the one method
// written without `static` that `::` reaches from outside its class.
TEST(ClassScopeResolutionElaboration, TheConstructorIsReachedFromOutside) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  function new(int v); x = v; endfunction\n"
      "endclass\n"
      "class D extends C;\n"
      "  function new(int v); super.new(v); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "  initial begin\n"
      "    c = D::new(4);\n"
      "    c = C::new(5);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §8.23: `Cfg::my_type` names the type Cfg declares and no other, so a module
// array typedef sharing the bare name lends x none of its dimensions; adopted,
// x would be a two-element array of one-bit logic, and `x = 5` an assignment
// of an integral value to it.
TEST(ClassScopeResolutionElaboration, ScopedTypedefTakesNoModuleArrayDims) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Cfg;\n"
      "  typedef int my_type;\n"
      "endclass\n"
      "module m;\n"
      "  typedef logic my_type [2];\n"
      "  Cfg::my_type x;\n"
      "  initial x = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  const auto* x = FindVar(design, "m", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 32u);
}

}  // namespace
