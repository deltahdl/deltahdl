#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(NettypeElaboration, NetCarriesNettypeIdentity) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype logic my_net;\n"
      "  my_net x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const RtlirNet* net = nullptr;
  for (const auto& n : mod->nets) {
    if (n.name == "x") net = &n;
  }
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->is_user_nettype);
  EXPECT_EQ(net->nettype_name, "my_net");
}

TEST(NettypeElaboration, NetCarriesResolutionFunction) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype logic [7:0] busnt with my_resolve;\n"
      "  busnt bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const RtlirNet* net = nullptr;
  for (const auto& n : mod->nets) {
    if (n.name == "bus") net = &n;
  }
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->is_user_nettype);
  EXPECT_EQ(net->resolve_func, "my_resolve");
}

TEST(NettypeElaboration, AliasNetInheritsResolutionFunction) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype logic [7:0] basent with my_resolve;\n"
      "  nettype basent aliasnt;\n"
      "  aliasnt n;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const RtlirNet* net = nullptr;
  for (const auto& nn : mod->nets) {
    if (nn.name == "n") net = &nn;
  }
  ASSERT_NE(net, nullptr);
  EXPECT_TRUE(net->is_user_nettype);
  EXPECT_EQ(net->resolve_func, "my_resolve");
}

static NettypeResolutionSig ConformingSig() {
  NettypeResolutionSig sig;
  sig.return_type_matches_nettype = true;
  sig.single_input_argument = true;
  sig.argument_is_input = true;
  sig.argument_is_dynamic_array = true;
  sig.argument_element_type_matches = true;
  sig.is_automatic = true;
  sig.is_class_method = false;
  sig.is_static_method = false;
  return sig;
}

TEST(NettypeElaboration, ResolutionFunctionWrongReturnTypeRejected) {
  auto sig = ConformingSig();
  sig.return_type_matches_nettype = false;
  EXPECT_EQ(ValidateNettypeResolutionFunction(sig),
            NettypeResolutionRule::kReturnType);
}

TEST(NettypeElaboration, ResolutionFunctionNonAutomaticRejected) {
  auto sig = ConformingSig();
  sig.is_automatic = false;
  EXPECT_EQ(ValidateNettypeResolutionFunction(sig),
            NettypeResolutionRule::kAutomaticLifetime);
}

TEST(NettypeElaboration, ResolutionFunctionNonStaticClassMethodRejected) {
  auto sig = ConformingSig();
  sig.is_class_method = true;
  sig.is_static_method = false;
  EXPECT_EQ(ValidateNettypeResolutionFunction(sig),
            NettypeResolutionRule::kClassStaticMethod);
}

TEST(NettypeElaboration, ResolutionFunctionStaticClassMethodAccepted) {
  auto sig = ConformingSig();
  sig.is_class_method = true;
  sig.is_static_method = true;
  EXPECT_EQ(ValidateNettypeResolutionFunction(sig),
            NettypeResolutionRule::kConforming);
}

TEST(NettypeElaboration, NonStaticClassMethodResolutionFunctionIsRejected) {
  ElabFixture f;
  Elaborate(
      "class C;\n"
      "  function logic [7:0] res(input logic [7:0] driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  nettype logic [7:0] wt with C::res;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function 'res' of user-defined nettype "
                            "'wt' shall be a static class method",
                            7, "6.6.7"));
}

TEST(NettypeElaboration, StaticClassMethodResolutionFunctionIsAccepted) {
  ElabFixture f;
  Elaborate(
      "class C;\n"
      "  static function logic [7:0] res(input logic [7:0] driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  nettype logic [7:0] wt with C::res;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(NettypeElaboration,
     ResolutionFunctionScopeNamingNeitherPackageNorClassRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype logic [7:0] wt with Nope::res;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function of user-defined nettype 'wt' "
                            "names unknown package or class 'Nope'",
                            2, "6.6.7"));
}

TEST(NettypeElaboration, ClassResolutionFunctionMissingFromItsClassRejected) {
  ElabFixture f;
  Elaborate(
      "class C;\n"
      "  static function logic [7:0] res(input logic [7:0] driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  nettype logic [7:0] wt with C::missing;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function 'C::missing' of user-defined "
                            "nettype 'wt' does not exist",
                            7, "6.6.7"));
}

TEST(NettypeElaboration,
     QualifiedResolutionFunctionDoesNotBindAnUnrelatedPlainFunction) {
  ElabFixture f;
  auto* design = Elaborate(
      "class C;\n"
      "  static function logic [7:0] res(input logic [7:0] driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  function logic [7:0] res(input logic [7:0] driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "  nettype logic [7:0] wt with C::res;\n"
      "  wt n;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirNet* net = FindNet(design, "m", "n");
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->resolve_func, "C::res");
}

TEST(NettypeElaboration, RealDataTypeAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype real rnt;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NettypeElaboration, StructDataTypeAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  nettype T wt;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NettypeElaboration, StringDataTypeRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype string snt;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'snt' is not a "
                            "legal nettype data type",
                            2, "6.6.7"));
}

TEST(NettypeElaboration, ChandleDataTypeRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype chandle cnt;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'cnt' is not a "
                            "legal nettype data type",
                            2, "6.6.7"));
}

TEST(NettypeElaboration, EventDataTypeRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype event ent;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'ent' is not a "
                            "legal nettype data type",
                            2, "6.6.7"));
}

TEST(NettypeElaboration, ConformingResolutionFunctionAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  function T Tsum(input T driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NettypeElaboration, ResolutionFunctionArgumentCountNamesItsOwnRule) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  function T Tsum(input T a[], input T b[]);\n"
      "    return a[0];\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall take a single input argument", 6, "6.6.7"));
}

TEST(NettypeElaboration, ResolutionFunctionReturnTypeNamesItsOwnRule) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  typedef struct { int other; } U;\n"
      "  function U Tsum(input T driver[]);\n"
      "    U u;\n"
      "    return u;\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall have a return type of 'T'", 8, "6.6.7"));
}

TEST(NettypeElaboration,
     ResolutionFunctionDynamicArrayArgumentNamesItsOwnRule) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  function T Tsum(input T driver[4]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a dynamic array rather than a fixed-size array", 6,
                            "6.6.7"));
}

TEST(NettypeElaboration, ResolutionFunctionOutputArgumentRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  function T Tsum(output T driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "and this one is not declared input", 6, "6.6.7"));
}

TEST(NettypeElaboration, ResolutionFunctionRefArgumentRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  function T Tsum(ref T driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "and this one is not declared input", 6, "6.6.7"));
}

TEST(NettypeElaboration,
     ResolutionFunctionArgumentElementTypeMismatchRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  typedef struct { int other; } U;\n"
      "  function T Tsum(input U driver[]);\n"
      "    T t;\n"
      "    return t;\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "dynamic array argument whose elements are of type 'T'", 8, "6.6.7"));
}

TEST(NettypeElaboration, ConformingResolutionFunctionStillAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  function automatic T Tsum(input T driver[]);\n"
      "    return driver[0];\n"
      "  endfunction\n"
      "  nettype T wt with Tsum;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(NettypeElaboration, TwoStateIntegralDataTypeAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype bit [3:0] bnt;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NettypeElaboration, ShortrealDataTypeAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  nettype shortreal snt;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NettypeElaboration, FixedUnpackedArrayDataTypeAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef bit AT[4];\n"
      "  nettype AT ant;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NettypeElaboration, ResolutionFunctionScopedByATypedefOfASpecialization) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  class Base #(parameter p = 1);\n"
             "    typedef struct { real r; bit [p-1:0] data; } S;\n"
             "    static function S Ssum(input S driver[]);\n"
             "      Ssum.r = 0.0;\n"
             "    endfunction\n"
             "  endclass\n"
             "  typedef Base#(32) MyBaseT;\n"
             "  nettype MyBaseT::S narrowTsum with MyBaseT::Ssum;\n"
             "  typedef MyBaseT alias_t;\n"
             "  nettype alias_t::S aliasTsum with alias_t::Ssum;\n"
             "endmodule\n"));
}

TEST(NettypeElaboration, ResolutionFunctionMissingFromATypedefsClassReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  class Base #(parameter p = 1);\n"
      "    typedef struct { real r; bit [p-1:0] data; } S;\n"
      "  endclass\n"
      "  typedef Base#(32) MyBaseT;\n"
      "  nettype MyBaseT::S narrowTsum with MyBaseT::Ssum;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "resolution function 'MyBaseT::Ssum' of "
                            "user-defined nettype 'narrowTsum' does not exist",
                            6, "6.6.7"));
}

constexpr const char* kCompilationUnitNettype =
    "nettype logic mynet;\n"
    "module top; mynet n; endmodule\n";

TEST(NettypeElaboration, ACompilationUnitNettypeIsDeclared) {
  ElabFixture f;
  auto* design = Elaborate(kCompilationUnitNettype, f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NettypeElaboration, ANetOfACompilationUnitNettypeCarriesIt) {
  ElabFixture f;
  auto* design = Elaborate(kCompilationUnitNettype, f);
  ASSERT_NE(design, nullptr);
  const RtlirNet* net = nullptr;
  for (const auto& n : design->top_modules[0]->nets) {
    if (n.name == "n") net = &n;
  }
  ASSERT_NE(net, nullptr);
  EXPECT_EQ(net->nettype_name, "mynet");
}

TEST(NettypeElaboration, NamedPackedVectorTypeFollowsAChainOfNames) {
  Arena arena;
  Expr left;
  Expr right;
  DataType vector;
  vector.kind = DataTypeKind::kLogic;
  vector.packed_dim_left = &left;
  vector.packed_dim_right = &right;
  DataType to_vector;
  to_vector.kind = DataTypeKind::kNamed;
  to_vector.type_name = "vec_net";
  DataType integer;
  integer.kind = DataTypeKind::kInteger;
  DataType enumeration;
  enumeration.kind = DataTypeKind::kEnum;
  enumeration.packed_dim_left = &left;
  enumeration.packed_dim_right = &right;
  DataType to_b;
  to_b.kind = DataTypeKind::kNamed;
  to_b.type_name = "b_t";
  DataType to_a;
  to_a.kind = DataTypeKind::kNamed;
  to_a.type_name = "a_t";
  const TypedefMap kTable{{"vec_net", vector},  {"alias_t", to_vector},
                          {"int_net", integer}, {"enum_t", enumeration},
                          {"a_t", to_b},        {"b_t", to_a}};

  DataType written;
  written.kind = DataTypeKind::kNamed;
  written.type_name = "alias_t";
  const DataType* found = NamedPackedVectorType(written, kTable, arena);
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->packed_dim_left, &left);
  EXPECT_EQ(found->packed_dim_right, &right);

  written.type_name = "int_net";
  EXPECT_EQ(NamedPackedVectorType(written, kTable, arena), nullptr);
  written.type_name = "enum_t";
  EXPECT_EQ(NamedPackedVectorType(written, kTable, arena), nullptr);
  written.type_name = "missing_t";
  EXPECT_EQ(NamedPackedVectorType(written, kTable, arena), nullptr);
  EXPECT_EQ(NamedPackedVectorType(to_a, kTable, arena), nullptr);
}

void ExpectIllegalNettypeDataType(const std::string& body) {
  ElabFixture f;
  const std::string kSrc =
      "module m;\n" + body + "  nettype bad_t n;\nendmodule\n";
  Elaborate(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'n' is not a "
                            "legal nettype data type",
                            LineHolding(kSrc, "nettype bad_t"), "6.6.7"));
}

TEST(NettypeElaboration, TypedefOfAStringDataTypeRejected) {
  ExpectIllegalNettypeDataType("  typedef string bad_t;\n");
}

TEST(NettypeElaboration, TypedefOfAClassDataTypeRejected) {
  ExpectIllegalNettypeDataType(
      "  class C; endclass\n"
      "  typedef C bad_t;\n");
}

TEST(NettypeElaboration, TypedefOfADynamicArrayDataTypeRejected) {
  ExpectIllegalNettypeDataType("  typedef logic [3:0] bad_t[];\n");
}

TEST(NettypeElaboration, TypedefOfAQueueOfRealDataTypeRejected) {
  ExpectIllegalNettypeDataType("  typedef real bad_t[$];\n");
}

TEST(NettypeElaboration, UnpackedStructWithAStringMemberDataTypeRejected) {
  ExpectIllegalNettypeDataType(
      "  typedef struct { real r; string s; } bad_t;\n");
}

TEST(NettypeElaboration, UnpackedStructWithAQueueMemberDataTypeRejected) {
  ExpectIllegalNettypeDataType("  typedef struct { real r[$]; } bad_t;\n");
}

TEST(NettypeElaboration, VoidDataTypeRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  nettype void vn;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'vn' is not a "
                            "legal nettype data type",
                            2, "6.6.7"));
}

TEST(NettypeElaboration, VirtualInterfaceDataTypeRejected) {
  ElabFixture f;
  Elaborate(
      "interface I; endinterface\n"
      "module m;\n"
      "  nettype virtual I vn;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'vn' is not a "
                            "legal nettype data type",
                            3, "6.6.7"));
}

TEST(NettypeElaboration, ClassDataTypeRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  class C; endclass\n"
      "  nettype C cn;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'cn' is not a "
                            "legal nettype data type",
                            3, "6.6.7"));
}

TEST(NettypeElaboration, FixedArrayOfARealAndTwoStateStructDataTypeAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef struct { real r; bit [3:0] b; struct { shortreal s; } n; } "
      "ok_t;\n"
      "  typedef ok_t ok_arr_t[2];\n"
      "  nettype ok_arr_t n5;\n"
      "  nettype n5 n6;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

bool NettypeAccepted(const std::string& decls, const std::string& type) {
  ElabFixture f;
  Elaborate("module m;\n" + decls + "  nettype " + type + " n;\nendmodule\n",
            f);
  return !f.has_errors;
}

TEST(NettypeElaboration, PackedStructureAndUnionDataTypesAccepted) {
  EXPECT_TRUE(NettypeAccepted("", "struct packed { logic [3:0] a; logic b; }"));
  EXPECT_TRUE(NettypeAccepted("", "struct packed { bit [3:0] a; bit b; }"));
  EXPECT_TRUE(NettypeAccepted(
      "  typedef union packed { logic [3:0] a; logic [3:0] b; } u4_t;\n",
      "u4_t"));
  EXPECT_TRUE(NettypeAccepted(
      "  typedef union packed { bit [3:0] a; bit [3:0] b; } u2_t;\n", "u2_t"));
}

TEST(NettypeElaboration, IntegralDataTypesAccepted) {
  EXPECT_TRUE(NettypeAccepted("", "logic [1:0][3:0]"));
  EXPECT_TRUE(NettypeAccepted("  typedef enum { A, B } e_t;\n", "e_t"));
  EXPECT_TRUE(NettypeAccepted("", "enum bit [1:0] { X, Y }"));
  for (const char* type :
       {"int", "integer", "byte", "shortint", "longint", "time", "reg [7:0]"}) {
    EXPECT_TRUE(NettypeAccepted("", type)) << type;
  }
}

TEST(NettypeElaboration, UnpackedUnionAndMultidimensionalArrayAccepted) {
  EXPECT_TRUE(NettypeAccepted(
      "  typedef union { real r; bit [63:0] b; } ru_t;\n", "ru_t"));
  EXPECT_TRUE(NettypeAccepted("", "union { real r; bit [63:0] b; }"));
  EXPECT_TRUE(NettypeAccepted("  typedef real r23_t [2][3];\n", "r23_t"));
  EXPECT_TRUE(NettypeAccepted("  typedef real r4_t [0:3];\n", "r4_t"));
}

TEST(NettypeElaboration, AssociativeArrayDataTypeRejected) {
  ExpectIllegalNettypeDataType("  typedef real bad_t[string];\n");
  ExpectIllegalNettypeDataType("  typedef real bad_t[int];\n");
  ExpectIllegalNettypeDataType("  typedef real bad_t[*];\n");
  ExpectIllegalNettypeDataType(
      "  typedef real fix_t[2];\n  typedef fix_t bad_t[int];\n");
}

TEST(NettypeElaboration, UnpackedUnionWithAnIllegalMemberRejected) {
  ExpectIllegalNettypeDataType(
      "  typedef union { real r; string s; } bad_t;\n");
  ExpectIllegalNettypeDataType(
      "  typedef union { real r; chandle c; } bad_t;\n");
  ExpectIllegalNettypeDataType("  typedef string bad_t [4];\n");
  ExpectIllegalNettypeDataType("  typedef event bad_t [2];\n");
}

TEST(NettypeElaboration, NestedDynamicArrayMemberRejected) {
  ExpectIllegalNettypeDataType(
      "  typedef struct { struct { int d[]; } inner; } bad_t;\n");
  ExpectIllegalNettypeDataType(
      "  typedef struct { int d[]; } in_t;\n"
      "  typedef struct { in_t inner; } bad_t;\n");
  EXPECT_TRUE(NettypeAccepted(
      "  typedef struct { struct { int d[2]; } inner; } ok_t;\n", "ok_t"));
}

TEST(NettypeElaboration, BuiltInClassAndCovergroupDataTypesRejected) {
  for (const char* type :
       {"mailbox", "semaphore", "std::semaphore", "std::mailbox"}) {
    ElabFixture f;
    const std::string kSrc =
        "module m;\n  nettype " + std::string(type) + " n;\nendmodule\n";
    Elaborate(kSrc, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "data type of user-defined nettype 'n' is not a "
                              "legal nettype data type",
                              2, "6.6.7"))
        << type;
  }
  ExpectIllegalNettypeDataType(
      "  covergroup cg; endgroup\n"
      "  typedef cg bad_t;\n");
  ElabFixture f;
  Elaborate(
      "covergroup ucg; endgroup\n"
      "module m;\n"
      "  nettype ucg n;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'n' is not a "
                            "legal nettype data type",
                            3, "6.6.7"));
}

TEST(NettypeElaboration, TypeParameterDataTypeJudgedAsItsType) {
  ElabFixture f;
  Elaborate(
      "module m #(parameter type T = string) ();\n"
      "  nettype T n;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "data type of user-defined nettype 'n' is not a "
                            "legal nettype data type",
                            2, "6.6.7"));
  EXPECT_TRUE(
      ElabOk("module c #(parameter type T = string) ();\n"
             "  nettype T n;\n"
             "endmodule\n"
             "module m;\n"
             "  c #(.T(real)) x();\n"
             "endmodule\n"));
  EXPECT_TRUE(NettypeAccepted("  parameter type P = real;\n", "P"));
  ExpectIllegalNettypeDataType("  parameter type bad_t = chandle;\n");
}

}  // namespace
