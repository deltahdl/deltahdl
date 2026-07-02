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

TEST(UserDefinedTypeElaboration, TypedefUnionWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union packed { logic [7:0] a; logic [7:0] b; } val_t;\n"
      "  val_t u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "u") {
      // A packed union sizes to its widest member; both members are 8 bits.
      EXPECT_EQ(v.width, 8u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
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

// §6.18: a forward typedef that specified the class basic type does not conform
// to a later definition of the same name that resolves to a non-class type, so
// redefining the name as a data typedef is an error.
TEST(UserDefinedTypeElaboration, ForwardClassTypedefWithDataDefinition_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef class C;\n"
      "  typedef int C;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.18: the same conformance rule applies to a forward interface-class
// typedef; a later data typedef of the same name does not conform.
TEST(UserDefinedTypeElaboration,
     ForwardInterfaceClassTypedefWithDataDefinition_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef interface class IC;\n"
      "  typedef int IC;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

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

// §6.18: the actual data type definition of a forward typedef shall be
// resolved within the same local scope OR generate block. Here a forward enum
// typedef, its final definition, and a variable using it all live inside a
// generate block; the definition resolves the forward declaration, so the
// variable's type is known and elaboration reports no error (an unresolved
// forward typedef would be an error, as UnresolvedForwardTypedefInModule_Error
// shows).
TEST(UserDefinedTypeElaboration, ForwardTypedefResolvedInGenerateBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  generate\n"
      "    for (i = 0; i < 1; i = i + 1) begin : g\n"
      "      typedef enum color_e;\n"
      "      typedef enum {RED, GREEN, BLUE} color_e;\n"
      "      color_e c;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

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
