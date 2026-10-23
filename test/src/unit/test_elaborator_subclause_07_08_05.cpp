#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(UserDefinedTypeAssocArrayElaboration, AssocArrayRealIndex_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[real];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            2, "7.8.5"));
}

TEST(UserDefinedTypeAssocArrayElaboration, AssocArrayShortrealIndex_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[shortreal];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            2, "7.8.5"));
}

TEST(UserDefinedTypeAssocArrayElaboration, EnumTypedefIndexAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  int aa[color_t];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_TRUE(v.is_assoc);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §7.8.5: equality is defined for a composite (struct) type and for the
// dynamically sized types it may contain, so such a type is a legal index.
// This mirrors the clause's own example of a struct holding an unsized
// dynamic-array member used as the index type.
TEST(UserDefinedTypeAssocArrayElaboration,
     StructIndexWithDynamicMemberAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef struct {byte B; int I[*];} unpkt_t;\n"
      "  int aa[unpkt_t];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_TRUE(v.is_assoc);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §7.8.5: a type that contains a real or shortreal has no defined equality
// operator and shall be an illegal index type, even when the real sits inside
// a struct member rather than being the index type itself.
TEST(UserDefinedTypeAssocArrayElaboration, StructIndexContainingRealRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {real r; int i;} mixed_t;\n"
      "  int aa[mixed_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            3, "7.8.5"));
}

// §7.8.5: the illegality of a real index type follows the type through a
// typedef chain, so an index named via a typedef that resolves to real is
// rejected just as a bare real would be.
TEST(UserDefinedTypeAssocArrayElaboration,
     TypedefResolvingToRealIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef real real_alias_t;\n"
      "  int aa[real_alias_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            3, "7.8.5"));
}

// §7.8.5: "contains a real" reaches through a struct member that is itself a
// typedef alias of real, so the real-ness has to be resolved before the index
// type can be judged legal. Such a struct is still an illegal index type.
TEST(UserDefinedTypeAssocArrayElaboration,
     StructMemberTypedefResolvingToRealRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef real real_alias_t;\n"
      "  typedef struct {real_alias_t r; int i;} mixed_t;\n"
      "  int aa[mixed_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            4, "7.8.5"));
}

// §7.8.5: "contains a real" reaches recursively through a nested aggregate. A
// struct member that is itself a named struct type holding a real makes the
// outer struct an illegal index type, so the check must descend into the inner
// struct's own members rather than stopping at the first level.
TEST(UserDefinedTypeAssocArrayElaboration,
     StructWithNestedTypedefStructContainingRealRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {real r;} inner_t;\n"
      "  typedef struct {inner_t x; int i;} outer_t;\n"
      "  int aa[outer_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            4, "7.8.5"));
}

// §7.8.5: an inline (anonymous) nested struct member is written directly in the
// enclosing struct rather than through a typedef, but a real buried inside that
// inline aggregate still makes the enclosing type contain a real and therefore
// an illegal index type.
TEST(UserDefinedTypeAssocArrayElaboration,
     StructWithInlineNestedStructContainingRealRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {struct {real r;} x; int i;} outer_t;\n"
      "  int aa[outer_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            3, "7.8.5"));
}

// Two packages each declare a `real_holder_t`, q's holding a real and r's
// not; the module imports one of them and declares `idx_t`, the index type,
// through the other's qualifier -- `typedef_line` being that declaration.
// §26.3 (printed page 808) reaches a package's declaration through its
// qualifier, so the qualified name is the named package's and never the
// imported bare name's. Found by the session that carried the qualifier to
// the type resolver (4af839bf7).
std::string TwoPackagesRealHolderIndex(std::string_view imported,
                                       std::string_view typedef_line) {
  return "package q;\n"
         "  typedef struct { real r; } real_holder_t;\n"
         "endpackage\n"
         "package r;\n"
         "  typedef struct { int r; } real_holder_t;\n"
         "endpackage\n"
         "module top;\n"
         "  import " +
         std::string(imported) + "::*;\n  " + std::string(typedef_line) +
         "\n"
         "  int aa[idx_t];\n"
         "endmodule\n";
}

// §7.8.5 with §26.3: the member `q::real_holder_t h` holds q's real although
// the imported bare `real_holder_t` is r's real-free structure. Looked up by
// the bare name, the member resolved to r's and the index type was not
// reported.
TEST(UserDefinedTypeAssocArrayElaboration,
     StructMemberQualifiedByAnotherPackageHoldingRealRejected) {
  ElabFixture f;
  ElaborateSrc(TwoPackagesRealHolderIndex(
                   "r", "typedef struct { q::real_holder_t h; int i; } idx_t;"),
               f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            10, "7.8.5"));
}

// The mirror: `r::real_holder_t h` holds no real although q's real-holding
// structure is what the imported bare name stands for, so the index type is
// legal; the bare lookup reported it.
TEST(UserDefinedTypeAssocArrayElaboration,
     StructMemberQualifiedByRealFreePackageAllowedDespiteImportedReal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      TwoPackagesRealHolderIndex(
          "q", "typedef struct { r::real_holder_t h; int i; } idx_t;"),
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.8.5 with §26.3 for a typedef of a qualified name rather than a member:
// `typedef r::real_holder_t idx_t` names r's real-free structure although the
// imported bare name is q's, so the index type is legal; ContainsRealType
// looked the alias up by the bare name and reported it.
TEST(UserDefinedTypeAssocArrayElaboration,
     TypedefOfQualifiedRealFreeTypeAllowedDespiteImportedReal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      TwoPackagesRealHolderIndex("q", "typedef r::real_holder_t idx_t;"), f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §7.8.5: the ban on a real index type holds for every associative dimension
// of a declaration, the second as much as the first, and through a typedef
// name standing for a type that holds a real.
TEST(AssocIndexTypeValidation, RealIndexTypeOnAnyDimensionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct { real r; } rs_t;\n"
      "  int a [real];\n"
      "  int b [2][real];\n"
      "  int c [int][rs_t];\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (uint32_t line = 3; line <= 5; ++line) {
    EXPECT_TRUE(ReportedError(diags,
                              "real or shortreal type shall not be used as an "
                              "associative array index type",
                              line, "7.8.5"));
  }
}

// §7.8.5: the same ban wherever the array is declared: a typedef in the
// compilation unit, a package variable, a class property, a subroutine's
// argument and a variable of a procedural block.
TEST(AssocIndexTypeValidation, RealIndexTypeRejectedInEveryScope) {
  ElabFixture f;
  ElaborateSrc(
      "typedef int t_real_idx [real];\n"
      "package p; int pa [real]; endpackage\n"
      "module top;\n"
      "  class C; int ca [real]; endclass\n"
      "  function void f(int fa [real]); endfunction\n"
      "  initial begin\n"
      "    int la [real];\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  const uint32_t kLines[] = {1, 2, 4, 5, 7};
  for (uint32_t line : kLines) {
    EXPECT_TRUE(ReportedError(diags,
                              "real or shortreal type shall not be used as an "
                              "associative array index type",
                              line, "7.8.5"));
  }
}

// §7.8 with §26.3 and §8.23: an index type named through a package or a class
// scope is the type the scope declares, so `a` takes a 4-bit unsigned index,
// `b` an 8-bit signed one and `k` a class index, while `p::N`, a constant,
// still sizes `z` at four. Each scoped index was dropped, and its variable
// built with no dimension.
TEST(UserDefinedTypeAssocArrayElaboration, ScopedTypeNameIndexIsAssociative) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  typedef bit [3:0] idx_t;\n"
      "  parameter int N = 4;\n"
      "  class K; endclass\n"
      "endpackage\n"
      "class C; typedef byte key_t; endclass\n"
      "module top;\n"
      "  int a [p::idx_t];\n"
      "  int b [C::key_t];\n"
      "  int k [p::K];\n"
      "  int z [p::N];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const auto& vars = design->top_modules[0]->variables;
  auto var = [&vars](std::string_view name) -> const RtlirVariable* {
    auto it = std::ranges::find(vars, name, &RtlirVariable::name);
    return it == vars.end() ? nullptr : &*it;
  };
  const RtlirVariable* a = var("a");
  const RtlirVariable* b = var("b");
  const RtlirVariable* k = var("k");
  const RtlirVariable* z = var("z");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  ASSERT_NE(k, nullptr);
  ASSERT_NE(z, nullptr);
  EXPECT_TRUE(a->is_assoc);
  EXPECT_EQ(a->assoc_index_width, 4u);
  EXPECT_FALSE(a->is_index_signed);
  EXPECT_TRUE(b->is_assoc);
  EXPECT_EQ(b->assoc_index_width, 8u);
  EXPECT_TRUE(b->is_index_signed);
  EXPECT_TRUE(k->is_assoc);
  EXPECT_TRUE(k->is_class_index);
  EXPECT_FALSE(z->is_assoc);
  EXPECT_EQ(z->unpacked_size, 4u);
}

// §7.8.5: a real index type is illegal however it is named, and a package's
// typedef of real is reached through its scope as a bare typedef is.
TEST(UserDefinedTypeAssocArrayElaboration, ScopedRealIndexIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "package q; typedef real real_t; endpackage\n"
      "module top;\n"
      "  int r [q::real_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "real or shortreal type shall not be used as an "
                            "associative array index type",
                            3, "7.8.5"));
}

// §6.7: a net's dimension is fixed-size, and an index type named through a
// package scope, a typedef's or a class's, makes an associative one, so each
// of w1 and w2 is reported. A range, which w3 writes, is fixed-size.
TEST(UserDefinedTypeAssocArrayElaboration, NetOfScopedIndexDimIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "package p; typedef bit [3:0] idx_t; class K; endclass endpackage\n"
      "module top;\n"
      "  wire w1 [p::idx_t];\n"
      "  wire w2 [p::K];\n"
      "  wire w3 [0:1];\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u, 5u}) {
    EXPECT_EQ(
        static_cast<bool>(ReportedError(
            f.diag.Diagnostics(),
            "a net's unpacked dimension must be fixed-size", line, "6.7")),
        line != 5u)
        << "line " << line;
  }
}

}  // namespace
