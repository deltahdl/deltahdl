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

TEST(CovergroupItemMethods, SampleOrSetInstNameOnAnItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  bit [1:0] a, b;\n"
      "  covergroup cg;\n"
      "    X: cross a, b;\n"
      "    cp: coverpoint a;\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial begin\n"
      "    c.cp.sample();\n"
      "    c.X.set_inst_name(\"n\");\n"
      "    c.sample();\n"
      "    c.cp.stop();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "sample() is a method of a covergroup instance, "
                            "not of its coverpoint or cross 'cp'",
                            9, "19.8"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "set_inst_name() is a method of a covergroup "
                            "instance, not of its coverpoint or cross 'X'",
                            10, "19.8"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

}  // namespace
