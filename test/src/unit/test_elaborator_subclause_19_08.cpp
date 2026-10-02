#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <tuple>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string TypeCallError(const char* method, const char* type) {
  return std::string("method '") + method +
         "' cannot be called through the covergroup type '" + type +
         "'; only get_coverage() can";
}

// §19.8: get_coverage() is the one static covergroup method, called through
// the covergroup type with `::` as well as on an instance; get_inst_coverage()
// is invoked only with `.`, and the other methods act on an instance. A call
// through the type to any of them, on the covergroup or on one of its
// coverpoints, is an error, whether the type is the module's own or one the
// compilation unit declares.
TEST(CovergroupTypeCalls, OnlyGetCoverageIsCalledThroughTheType) {
  ElabFixture f;
  ElaborateSrc(
      "covergroup ucg with function sample(bit a);\n"
      "  ua : coverpoint a;\n"
      "endgroup\n"
      "module m;\n"
      "  bit v;\n"
      "  real r;\n"
      "  covergroup gc;\n"
      "    ca : coverpoint v;\n"
      "  endgroup\n"
      "  gc g = new;\n"
      "  initial begin\n"
      "    gc::stop();\n"
      "    r = gc::get_inst_coverage();\n"
      "    gc::ca::start();\n"
      "    ucg::sample(1);\n"
      "    r = gc::get_coverage() + gc::ca::get_coverage();\n"
      "    r = ucg::get_coverage() + g.get_inst_coverage();\n"
      "  end\n"
      "endmodule\n",
      f);
  for (auto [line, method, type] :
       std::initializer_list<std::tuple<uint32_t, const char*, const char*>>{
           {12u, "stop", "gc"},
           {13u, "get_inst_coverage", "gc"},
           {14u, "start", "gc"},
           {15u, "sample", "ucg"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), TypeCallError(method, type),
                              line, "19.8"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

// §19.8 with §8.23: a covergroup type the module declares is a base of `::`,
// so its coverage and that of its coverpoint are read through it on the right
// side of an assignment as on that of any other.
TEST(CovergroupTypeCalls, AModulesCovergroupTypeIsABaseOfTheScopeOperator) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit v;\n"
      "  real r;\n"
      "  covergroup gc;\n"
      "    ca : coverpoint v;\n"
      "  endgroup\n"
      "  gc g = new;\n"
      "  initial begin\n"
      "    r = gc::get_coverage();\n"
      "    r = gc::ca::get_coverage();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.8 with §26.3: a covergroup type a wildcard import makes visible is
// called through as the module's own is, and a class's static method called
// through the class is no covergroup's.
TEST(CovergroupTypeCalls, AnImportedTypeIsCalledThroughAsTheModulesOwn) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  covergroup pcg with function sample(bit a);\n"
      "    pa : coverpoint a;\n"
      "  endgroup\n"
      "endpackage\n"
      "class C;\n"
      "  static function void stop(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  import p::*;\n"
      "  initial begin\n"
      "    pcg::set_inst_name(\"x\");\n"
      "    C::stop();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            TypeCallError("set_inst_name", "pcg"), 12u,
                            "19.8"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
