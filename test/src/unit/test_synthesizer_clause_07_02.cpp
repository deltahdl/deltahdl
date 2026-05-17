#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/aig.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

// §7.2 BNF: `struct_union [ packed [ signing ] ] { struct_union_member ... }`
// describes the data_type form for a struct. Synthesis must accept a struct
// declaration as a valid variable type and produce an AIG.
TEST(StructDeclarationSynthesis, PackedStructDeclLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  assign p = '{8'hAB, 8'hCD};\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

// §7.2 BNF: a struct member can itself be a struct (the data_type_or_void
// inside struct_union_member admits the full data_type production). Confirm
// the synthesizer handles a nested-struct declaration.
TEST(StructDeclarationSynthesis, NestedPackedStructLowers) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  typedef struct packed { logic [3:0] x; logic [3:0] y; } point_t;\n"
      "  typedef struct packed { point_t p; logic [7:0] tag; } record_t;\n"
      "  record_t r;\n"
      "  assign r = '{p: '{x: 4'h1, y: 4'h2}, tag: 8'hAA};\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
