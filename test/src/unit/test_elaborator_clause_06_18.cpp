#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(UserDefinedTypeElaboration, TypedefNamedResolution) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef logic [15:0] word_t;\n"
      "  word_t data;\n"
      "  initial data = 1234;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "data") {
      EXPECT_EQ(v.width, 16u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(UserDefinedTypeElaboration, TypedefChain) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef byte_t octet_t;\n"
      "  octet_t val;\n"
      "  initial val = 255;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "val") {
      EXPECT_EQ(v.width, 8u);
      EXPECT_TRUE(v.is_4state);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(UserDefinedTypeElaboration, TypedefChainSigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef int my_int;\n"
      "  my_int x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  for (const auto& v : mod->variables) {
    if (v.name == "x") {
      EXPECT_EQ(v.width, 32u);
      EXPECT_TRUE(v.is_signed);
    }
  }
}

TEST(UserDefinedTypeElaboration, TypedefStructWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  for (const auto& v : mod->variables) {
    if (v.name == "p") {
      EXPECT_EQ(v.width, 16u);
    }
  }
}

TEST(UserDefinedTypeElaboration, ForwardTypedefThenDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum color_e;\n"
      "  typedef enum {RED, GREEN, BLUE} color_e;\n"
      "  color_e c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UserDefinedTypeElaboration, BareForwardTypedefThenDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef my_type;\n"
      "  typedef int my_type;\n"
      "  my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UserDefinedTypeElaboration, TypedefChain2State) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef bit [7:0] ubyte_t;\n"
      "  typedef ubyte_t alias_t;\n"
      "  alias_t val;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  for (const auto& v : mod->variables) {
    if (v.name == "val") {
      EXPECT_EQ(v.width, 8u);
      EXPECT_FALSE(v.is_4state);
    }
  }
}

// §6.18: "It shall be legal to have multiple forward type declarations for
// the same type identifier in the same scope." The forward declarations are
// resolved by the matching class declaration that follows.
TEST(UserDefinedTypeElaboration, MultipleForwardTypedefsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef class myclass;\n"
      "  typedef class myclass;\n"
      "  class myclass;\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.18: "It shall be an error if a basic data type was specified by the
// forward type declaration and the actual type definition does not conform
// to the specified basic data type."
TEST(UserDefinedTypeElaboration, ForwardEnumWithStructDefinition_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef enum my_t;\n"
      "  typedef struct packed { int A; int B; } my_t;\n"
      "  my_t x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UserDefinedTypeElaboration, ForwardStructWithEnumDefinition_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct my_t;\n"
      "  typedef enum {RED, GREEN, BLUE} my_t;\n"
      "  my_t x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UserDefinedTypeElaboration, ForwardUnionWithEnumDefinition_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef union my_t;\n"
      "  typedef enum {A, B} my_t;\n"
      "  my_t x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.18: "It shall be legal to have multiple forward type declarations for
// the same type identifier in the same scope." This case exercises the
// kind-keyword form (`typedef enum NAME;`) with multiple forwards, all
// resolved by a single final enum definition.
TEST(UserDefinedTypeElaboration, MultipleForwardEnumDeclarations) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef enum color_e;\n"
      "  typedef enum color_e;\n"
      "  typedef enum {RED, GREEN, BLUE} color_e;\n"
      "  color_e c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.18: "It shall be legal to have a forward type declaration in the same
// scope, either before or after the final type definition." The forward
// declaration appearing after the real definition must not corrupt the
// existing type so that subsequent variable declarations still resolve.
TEST(UserDefinedTypeElaboration, ForwardTypedefAfterFinalDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  typedef struct pair_t;\n"
      "  pair_t p;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "p") {
      EXPECT_EQ(v.width, 16u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §6.18: "It shall be an error if the type_identifier does not resolve to a
// data type." A forward enum/struct/union declaration with no matching real
// definition in the same scope is unresolved.
TEST(UserDefinedTypeElaboration, UnresolvedForwardTypedefInModule_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef enum color_e;\n"
      "  color_e c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.18: A bare forward typedef (`typedef NAME;`) with no matching real
// definition in the same scope is similarly unresolved.
TEST(UserDefinedTypeElaboration, UnresolvedBareForwardTypedefInModule_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef my_type;\n"
      "  my_type x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.18: "It shall be an error if the prefix does not resolve to a class."
// `T_fwd` is forward-declared and then resolved as `int`, so using it as a
// class scope-resolution prefix in `T_fwd::Inner` is an error.
TEST(UserDefinedTypeElaboration, ForwardTypedefScopePrefixNotClass_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef T_fwd;\n"
      "  typedef int T_fwd;\n"
      "  typedef T_fwd::Inner inner_t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.18 positive companion to the above: when the forward-declared prefix
// resolves to a class, using it as a scope-resolution prefix in a typedef
// declaration is legal.
TEST(UserDefinedTypeElaboration, ForwardTypedefScopePrefixClass_Legal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef class C;\n"
      "  class C;\n"
      "    typedef int T;\n"
      "  endclass\n"
      "  typedef C::T t_alias;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
