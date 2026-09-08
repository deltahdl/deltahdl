#include <cstdint>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassObjectElaboration, ForwardTypedefClassOk) {
  EXPECT_TRUE(
      ElabOk("typedef class C2;\n"
             "class C1;\n"
             "  C2 c;\n"
             "endclass\n"
             "class C2;\n"
             "  C1 c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassWithoutForwardTypedefOk) {
  EXPECT_TRUE(
      ElabOk("class MyClass;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ForwardTypedefInterfaceClassOk) {
  EXPECT_TRUE(
      ElabOk("typedef interface class IC;\n"
             "interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §6.18 carries the rule: "The actual data type definition of a forward typedef
// declaration shall be resolved within the same local scope or generate block."
// §8.27 restates it for a forward class declaration and says so, opening "As
// with other forward typedefs as described in 6.18", so both sites pass
// Subclause("6.18"). Elaborator::ValidateForwardClassTypedefs in
// src/elaborator/elaborator_validate_classes.cpp walks the compilation unit's
// items and Elaborator::ValidateForwardTypedefsInScope in
// src/elaborator/elaborator_scope_rules_enclosing.cpp walks a ModuleDecl's
// items; the two lists are disjoint, and that is what tells the two sites
// apart. This source declares its forward typedef at compilation-unit scope, so
// only the first site reaches it.
TEST(ClassObjectElaboration, UnresolvedForwardTypedefClassError) {
  ElabFixture f;
  ElabOk(
      "typedef class C2;\n"
      "class C1;\n"
      "  C2 c;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is never resolved by a definition in the same scope", 1, "6.18"));
}

// §8.27: the bare `typedef C2;` form is equivalent to `typedef class C2;` and
// shall work the same way. Equivalence includes the resolution rule: an
// unresolved bare forward typedef must be rejected by the same production path
// that rejects the class-keyword form (see UnresolvedForwardTypedefClassError).
TEST(ClassObjectElaboration, UnresolvedBareForwardTypedefClassError) {
  ElabFixture f;
  ElabOk(
      "typedef C2;\n"
      "class C1;\n"
      "  C2 c;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is never resolved by a definition in the same scope", 1, "6.18"));
}

TEST(ClassObjectElaboration, ForwardTypedefParameterizedClassOk) {
  EXPECT_TRUE(
      ElabOk("typedef class C;\n"
             "module top;\n"
             "  C#(1, real) v2;\n"
             "  C#(.p(2), .T(real)) v3;\n"
             "endmodule\n"
             "class C #(parameter p = 2, type T = int);\n"
             "endclass\n"));
}

TEST(ClassObjectElaboration, BareForwardTypedefWithoutClassKeywordOk) {
  EXPECT_TRUE(
      ElabOk("typedef C2;\n"
             "class C1;\n"
             "  C2 c;\n"
             "endclass\n"
             "class C2;\n"
             "  C1 c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §8.27's forward declaration introduces the name before the type: `typedef
// class C;` says C is a class and nothing else, so the elaborated table has no
// width to record for it. It recorded 1, which is §6.10's answer for the
// implicit type a forward declaration leaves behind and is not what a class is
// -- §8.3 makes a class variable a handle to an object, which this simulator
// carries in 64 bits.
//
// What made that worth answering at the table is that it turned on an unrelated
// declaration: a class the design does not forward-declare is in no typedef map
// at all, so its name answers 0, and the same class name answered 1 in a file
// that happened to write the forward declaration. The vector typedef beside it
// is the control -- a name that does have a width still records it -- and the
// absent entry is told from a recorded 0, so "no width" reads as an answer
// rather than as the name never having reached the table.
TEST(ClassObjectElaboration, ForwardDeclaredClassIsRecordedWithNoWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef class C;\n"
      "typedef logic [7:0] byte_t;\n"
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  byte_t v;\n"
      "  initial v = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto width_of = [design](std::string_view name) -> int64_t {
    auto it = design->type_widths.find(name);
    if (it == design->type_widths.end()) return -1;
    return it->second;
  };
  EXPECT_EQ(width_of("byte_t"), 8);
  EXPECT_EQ(width_of("C"), 0);
}

}  // namespace
