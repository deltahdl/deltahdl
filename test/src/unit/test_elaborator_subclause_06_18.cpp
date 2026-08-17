#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typedef 'my_t' does not conform to its forward declaration as enum", 3,
      "6.18"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typedef 'my_t' does not conform to its forward declaration as struct", 3,
      "6.18"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typedef 'my_t' does not conform to its forward declaration as union", 3,
      "6.18"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typedef 'C' does not conform to its forward declaration as class", 3,
      "6.18"));
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
  // Parser::TryForwardClassTypedef records kNamed for the interface-class form
  // too, so the report names the same "class" noun the plain class form gets.
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typedef 'IC' does not conform to its forward declaration as class", 3,
      "6.18"));
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
  // Elaborator::ValidateForwardTypedefsInScope and
  // Elaborator::ValidateForwardClassTypedefs emit this sentence word for word,
  // both under §6.18. They walk disjoint item lists: the first a ModuleDecl's
  // items, the second the compilation unit's. This forward typedef is inside a
  // module, so only the first reaches it.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "forward typedef 'color_e' is never resolved by a "
                            "definition in the same scope",
                            2, "6.18"));
}

TEST(UserDefinedTypeElaboration, UnresolvedBareForwardTypedefInModule_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef my_type;\n"
      "  my_type x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "forward typedef 'my_type' is never resolved by a "
                            "definition in the same scope",
                            2, "6.18"));
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
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "scope-resolution prefix 'T_fwd' of a typedef does not "
                    "resolve to a class",
                    4, "6.18"));
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

// §6.18: a typedef "gives a user-defined name to an existing data type", and
// the clause counts unpacked array types among those -- it notes that a
// user-defined name is needed for a type parameter value "when unpacked array
// types are used". A variable declared with such a name is therefore of that
// array type, dimensions included, and a queue dimension makes it a queue.
TEST(UserDefinedTypeElaboration, QueueTypedefDeclaresAQueue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef string T_SQ[$];\n"
      "  T_SQ sq;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_queue);
}

// The same rule for the other unsized dimension. §7.4 makes `[]` a dynamic
// array, and neither it nor a queue has a fixed width -- which is what had kept
// both from being carried across the typedef while the fixed form was.
TEST(UserDefinedTypeElaboration, DynamicArrayTypedefDeclaresADynamicArray) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int T_DA[];\n"
      "  T_DA da;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_dynamic);
}

// The fixed form, which already worked, as the guard that widening the
// recording to the unsized dimensions did not disturb it: a sized typedef
// dimension still gives the variable that many elements and leaves it neither a
// queue nor a dynamic array.
TEST(UserDefinedTypeElaboration, FixedArrayTypedefStillSizesTheVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int T_FA[3];\n"
      "  T_FA fa;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  const auto& vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_EQ(vars[0].unpacked_size, 3u);
  EXPECT_FALSE(vars[0].is_queue);
  EXPECT_FALSE(vars[0].is_dynamic);
}

// ---------------------------------------------------------------------------
// Claim: "The declaration of a user-defined data type shall precede any
// reference to its type_identifier."
//
// The three cases below are the ones the parser cannot answer, because
// `my_type x;` is the two identifiers and semicolon a module instantiation
// missing its port connection list also spells, and the parser holds no table
// of module names. Each asserts the §6.18 report rather than the §23.3.2 one
// the missing port connection list would draw.
// ---------------------------------------------------------------------------

// The typedef stands below the declaration that references it, so the type is
// resolvable by the time the module is elaborated and the variable takes the
// right width. §6.18 is breached all the same: what the sentence forbids is the
// order, not the failure to resolve.
TEST(UserDefinedTypeElaboration, TypeReferenceBeforeItsDeclarationIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  my_type x;\n"
      "  typedef int my_type;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 'my_type' does not precede "
                            "this reference to it",
                            2, "6.18"));
}

// A name declared nowhere at all. §6.18 draws no distinction between a
// declaration written below the reference and one never written: neither
// precedes the reference. Reporting it as an unknown module instead would name
// a construct the source does not contain, since nothing here is instantiated.
TEST(UserDefinedTypeElaboration,
     NameThatIsNeitherTypeNorModuleIsReportedAsAnUndeclaredType) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  nosuch x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 'nosuch' does not precede "
                            "this reference to it",
                            2, "6.18"));
}

// The type is declared, in a package the module never imports, so no
// declaration of it precedes the reference in the scope the reference stands
// in. This is the case a repair keyed on the declaration coming later in the
// same file would miss.
TEST(UserDefinedTypeElaboration,
     TypeDeclaredInAPackageNeverImportedIsStillAnUndeclaredTypeReference) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  typedef int my_type;\n"
      "endpackage\n"
      "module m;\n"
      "  my_type x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 'my_type' does not precede "
                            "this reference to it",
                            5, "6.18"));
}

}  // namespace
