#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(ParameterizedTypeSynthesis, TypeParamSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "class C #(type T = int);\n"
      "  typedef T my_type;\n"
      "endclass\n"
      "module m;\n"
      "  C#(logic [7:0])::my_type x;\n"
      "  assign x = 8'h00;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ParameterizedTypeSynthesis, ValueParamSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "virtual class bus_def #(parameter WIDTH = 8);\n"
      "  typedef logic [WIDTH-1:0] data_t;\n"
      "endclass\n"
      "module m(input logic [15:0] d, output logic [15:0] q);\n"
      "  bus_def#(16)::data_t w;\n"
      "  assign w = d;\n"
      "  assign q = w;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(ParameterizedTypeSynthesis, DistinctSpecializationsSynthesize) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "virtual class bus_def #(parameter WIDTH = 8);\n"
      "  typedef logic [WIDTH-1:0] data_t;\n"
      "endclass\n"
      "module m(input logic [7:0] a, input logic [15:0] b,\n"
      "         output logic [7:0] x, output logic [15:0] y);\n"
      "  bus_def#(8)::data_t narrow;\n"
      "  bus_def#(16)::data_t wide;\n"
      "  assign narrow = a;\n"
      "  assign wide = b;\n"
      "  assign x = narrow;\n"
      "  assign y = wide;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
