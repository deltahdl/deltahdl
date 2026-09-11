#include <cstdint>
#include <string_view>

#include "fixture_elaborator.h"

using namespace delta;

// A.2 "Declarations" writes no production of its own; it is a heading over
// A.2.1 through A.2.12, and each of those has a file here that drives the forms
// it writes. What the section itself has to say is that they are one section: a
// declaration A.2 defines is that declaration wherever the grammar admits it,
// carrying the same parts and meaning the same thing in each place.
//
// `specparam_declaration` is where that is checkable from the elaborated
// design, because A.2.1.1 writes the production once -
//
//     specparam_declaration ::=
//         specparam [ packed_dimension ] list_of_specparam_assignments ;
//
// - while §6.20.5 admits it in two places: "A specparam ... may be declared
// inside a specify block or in the module body." Two declaration sites, one
// production, so a specparam written in a specify block is as wide as the same
// declaration written in the module body and no other rule applies to it.

namespace {

// The width of the elaborated variable a specparam declaration produced, or 0
// where the module holds no variable of that name.
uint32_t WidthOfVariable(const RtlirModule* mod, std::string_view name) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return v.width;
  }
  return 0;
}

// The optional packed dimension is part of the one production, so it reaches
// the declaration at both sites. Inside a specify block it was parsed and
// dropped and the specparam recorded 32 bits wide, so a design writing the same
// `[7:0] = 5` in the two places §6.20.5 admits got an 8-bit constant from one
// of them and a 32-bit constant from the other.
TEST(DeclarationSectionElaboration, ARangeSizesASpecparamAtEitherSite) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam [7:0] tBody = 5;\n"
      "  specify\n"
      "    specparam [7:0] tSpec = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* mod = design->top_modules[0];
  EXPECT_EQ(WidthOfVariable(mod, "tBody"), 8u);
  EXPECT_EQ(WidthOfVariable(mod, "tSpec"), WidthOfVariable(mod, "tBody"));
}

// And the rule that applies when the production's range is left out: §6.20.5
// gives such a specparam "the range of its final value", which for a 4-bit
// sized literal is 4 bits. That reading is of the declaration rather than of
// where it stands, so the specify-block site takes it too; that site had
// answered 32 for every specparam, which is neither the declared range nor the
// value's.
TEST(DeclarationSectionElaboration,
     AValueSizesARangelessSpecparamAtEitherSite) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specparam tBody = 4'd5;\n"
      "  specify\n"
      "    specparam tSpec = 4'd5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* mod = design->top_modules[0];
  EXPECT_EQ(WidthOfVariable(mod, "tBody"), 4u);
  EXPECT_EQ(WidthOfVariable(mod, "tSpec"), WidthOfVariable(mod, "tBody"));
}

// One range governs the whole list the production writes after it, at the
// specify-block site as at the other: `list_of_specparam_assignments` is inside
// the declaration the range opens, so every assignment of it is that wide.
TEST(DeclarationSectionElaboration, OneRangeGovernsTheWholeAssignmentList) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  specify\n"
      "    specparam [3:0] tRise = 1, tFall = 2;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* mod = design->top_modules[0];
  EXPECT_EQ(WidthOfVariable(mod, "tRise"), 4u);
  EXPECT_EQ(WidthOfVariable(mod, "tFall"), 4u);
}

}  // namespace
