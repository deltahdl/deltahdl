#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §19.7.1: strobe and real_interval can be set only in the covergroup
// definition; a procedural write to either through the covergroup type, at the
// covergroup's level or a coverpoint's, is an error. Every other type option,
// merge_instances and weight among them, can be assigned during simulation.
TEST(TypeOptionWrites, DefinitionOnlyTypeOptionWrittenProcedurallyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [2:0] x;\n"
      "  covergroup cg;\n"
      "    a: coverpoint x;\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial begin\n"
      "    cg::type_option.strobe = 1;\n"
      "    cg::type_option.real_interval = 2.0;\n"
      "    cg::a::type_option.real_interval = 2.0;\n"
      "    cg::type_option.merge_instances = 1;\n"
      "    cg::a::type_option.weight = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (auto [line, member] :
       std::initializer_list<std::pair<uint32_t, const char*>>{
           {8u, "strobe"}, {9u, "real_interval"}, {10u, "real_interval"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("type option '") + member +
                                  "' can be set only in the covergroup "
                                  "definition",
                              line, "19.7.1"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

// §19.7.1: the rule binds a write through a covergroup type alone; a class's
// static struct named type_option takes a strobe member like any other.
TEST(TypeOptionWrites, ClassMemberNamedTypeOptionIsAssignable) {
  ElabFixture f;
  ElaborateSrc(
      "class k;\n"
      "  typedef struct { int strobe; } opt_t;\n"
      "  static opt_t type_option;\n"
      "endclass\n"
      "module m;\n"
      "  initial k::type_option.strobe = 1;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.7.1: a type option is set with a constant expression, so a module
// variable or a call of a function reading one is an error there, while a
// parameter and a function reading only a parameter are not.
TEST(TypeOptionValues, NonConstantValueIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a;\n"
      "  int w = 3;\n"
      "  parameter int P = 2;\n"
      "  function int f(); return w; endfunction\n"
      "  function int g(); return P; endfunction\n"
      "  covergroup cg;\n"
      "    type_option.weight = w;\n"
      "    ca: coverpoint a { type_option.goal = f(); }\n"
      "    cb: coverpoint a { type_option.weight = P + g(); }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type option 'weight' is set with 'w', which is no "
                            "constant",
                            8, "19.7.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "type option 'goal' is set with a call of 'f', "
                            "which is no constant function call",
                            9, "19.7.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

}  // namespace
