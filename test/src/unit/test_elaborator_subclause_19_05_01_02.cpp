#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "elaborator/coverpoint_bin_set_expression.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

// §19.5.1.2: a set_covergroup_expression may yield any array whose element type
// is assignment compatible with the coverpoint type. An integral element type
// is assignment compatible with an integral coverpoint.
TEST(CoverpointBinSetExpression, ElementTypeAssignmentCompatibleIsAllowed) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kInt;
  DataType element_type;
  element_type.kind = DataTypeKind::kByte;

  EXPECT_TRUE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

// §19.5.1.2: an element type that is not assignment compatible with the
// coverpoint type is rejected. A string element type cannot be assigned to an
// integral coverpoint.
TEST(CoverpointBinSetExpression, IncompatibleElementTypeIsRejected) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kInt;
  DataType element_type;
  element_type.kind = DataTypeKind::kString;

  EXPECT_FALSE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

// §19.5.1.2: the coverpoint type is not restricted to integral -- a coverpoint
// may be a real type (§19.5), and a real element type is assignment compatible
// with a real coverpoint, so a set expression yielding a real array is allowed.
TEST(CoverpointBinSetExpression, RealCoverpointAcceptsRealElement) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kReal;
  DataType element_type;
  element_type.kind = DataTypeKind::kReal;

  EXPECT_TRUE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

// §19.5.1.2: an element type that is not assignment compatible with a real
// coverpoint is still rejected -- a string element cannot be assigned to a real
// coverpoint, exercising the reject path in the real coverpoint domain.
TEST(CoverpointBinSetExpression, RealCoverpointRejectsStringElement) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kReal;
  DataType element_type;
  element_type.kind = DataTypeKind::kString;

  EXPECT_FALSE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

// §19.5.1.2: assignment compatibility spans the integral/real boundary, so a
// real coverpoint admits an integral element type -- the integral values are
// assignment compatible with the real coverpoint. This exercises the
// cross-domain assignment-compatibility path, distinct from the same-domain
// integral and real cases above.
TEST(CoverpointBinSetExpression, RealCoverpointAcceptsIntegralElement) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kReal;
  DataType element_type;
  element_type.kind = DataTypeKind::kInt;

  EXPECT_TRUE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

// §19.5.1.2: the cross-domain path holds in the other direction as well -- an
// integral coverpoint admits a real element type, since a real value is
// assignment compatible with an integral coverpoint.
TEST(CoverpointBinSetExpression, IntegralCoverpointAcceptsRealElement) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kInt;
  DataType element_type;
  element_type.kind = DataTypeKind::kReal;

  EXPECT_TRUE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

// §19.5.1.2: every array kind (fixed-size, dynamic, queue) is permitted.
TEST(CoverpointBinSetExpression, NonAssociativeArrayKindsAreAllowed) {
  EXPECT_TRUE(
      SetExpressionArrayKindAllowed(SetExpressionArrayKind::kFixedSize));
  EXPECT_TRUE(SetExpressionArrayKindAllowed(SetExpressionArrayKind::kDynamic));
  EXPECT_TRUE(SetExpressionArrayKindAllowed(SetExpressionArrayKind::kQueue));
}

// §19.5.1.2: associative arrays are the one exception that is not permitted.
TEST(CoverpointBinSetExpression, AssociativeArrayKindIsRejected) {
  EXPECT_FALSE(
      SetExpressionArrayKindAllowed(SetExpressionArrayKind::kAssociative));
}

// §19.5.1.2: identifiers declared within the covergroup (coverpoint identifiers
// and bin identifiers) are not visible within the expression.
TEST(CoverpointBinSetExpression, CovergroupLocalNamesAreNotVisible) {
  EXPECT_FALSE(
      SetExpressionNameVisible(SetExpressionNameOrigin::kCoverpointIdentifier));
  EXPECT_FALSE(
      SetExpressionNameVisible(SetExpressionNameOrigin::kBinIdentifier));
}

// §19.5.1.2: a name declared outside the covergroup remains visible.
TEST(CoverpointBinSetExpression, ExternalNameIsVisible) {
  EXPECT_TRUE(SetExpressionNameVisible(SetExpressionNameOrigin::kExternal));
}

// §19.5.1.2: the array a set_covergroup_expression yields may be of any kind
// but associative. A module's associative array is reported where a bin reads
// it; its fixed-size, dynamic and queue arrays are accepted.
TEST(CoverpointBinSetExpression, AssociativeArrayOfModuleIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [3:0] x;\n"
      "  int aa[int];\n"
      "  int wild[*];\n"
      "  int fixed_a[3];\n"
      "  int dyn[];\n"
      "  int q[$];\n"
      "  covergroup cg;\n"
      "    a: coverpoint x { bins s[] = aa; }\n"
      "    b: coverpoint x { bins s[] = wild; }\n"
      "    c: coverpoint x { bins f[] = fixed_a; bins d[] = dyn; bins u[] = q; "
      "}\n"
      "  endgroup\n"
      "  cg cv = new;\n"
      "endmodule\n",
      f);
  for (auto [line, name] : {std::pair<uint32_t, const char*>{9u, "aa"},
                            std::pair<uint32_t, const char*>{10u, "wild"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("the associative array '") + name +
                                  "' cannot define the bins of a "
                                  "set_covergroup_expression",
                              line, "19.5.1.2"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

// §19.5.1.2: the rule binds a covergroup embedded in a class (§19.4) as well;
// there the array read is a property of the class.
TEST(CoverpointBinSetExpression, AssociativeArrayOfClassIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class k;\n"
      "  bit [3:0] x;\n"
      "  int aa[string];\n"
      "  int dyn[];\n"
      "  covergroup cg;\n"
      "    a: coverpoint x { bins s[] = aa; bins d[] = dyn; }\n"
      "  endgroup\n"
      "  function new; cg = new; endfunction\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the associative array 'aa' cannot define the "
                            "bins of a set_covergroup_expression",
                            6, "19.5.1.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

// §19.5.1.2: a coverpoint identifier and a bin identifier, of a coverpoint or
// of a cross, declared within the covergroup are not visible in a
// set_covergroup_expression, so a bin naming one reads nothing. A name
// declared outside the covergroup is read.
TEST(CoverpointBinSetExpression, CovergroupOwnNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [3:0] x;\n"
      "  int vals[] = '{1, 2};\n"
      "  covergroup cg;\n"
      "    a: coverpoint x { bins lo = {1}; }\n"
      "    b: coverpoint x { bins s[] = a; }\n"
      "    c: coverpoint x { bins t[] = lo; }\n"
      "    d: coverpoint x { bins u[] = vals; }\n"
      "    ad: cross a, d { option.weight = 2; bins xb = binsof(a); }\n"
      "    e: coverpoint x { bins v[] = xb; }\n"
      "  endgroup\n"
      "  cg cv = new;\n"
      "endmodule\n",
      f);
  for (auto [line, name] : {std::pair<uint32_t, const char*>{6u, "a"},
                            std::pair<uint32_t, const char*>{7u, "lo"},
                            std::pair<uint32_t, const char*>{10u, "xb"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("'") + name +
                                  "' is declared within covergroup 'cg' and "
                                  "is not visible in a "
                                  "set_covergroup_expression",
                              line, "19.5.1.2"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

// §19.5.1.2: a bin identifier hides nothing from a set_covergroup_expression,
// so where a variable outside the covergroup shares the bin's name, the
// expression reads the variable.
TEST(CoverpointBinSetExpression, OuterNameSharingABinNameIsRead) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [3:0] x;\n"
      "  int lo[] = '{1, 2};\n"
      "  covergroup cg;\n"
      "    a: coverpoint x { bins lo = {1}; }\n"
      "    b: coverpoint x { bins s[] = lo; }\n"
      "  endgroup\n"
      "  cg cv = new;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.5.1.2 with §7.8: an associative array's index may be a type the module
// declares, a typedef or a class; a dimension naming a parameter declares a
// fixed-size array, and packed dimensions alone a packed array (§7.4.1), either
// of which a set_covergroup_expression may yield.
TEST(CoverpointBinSetExpression, IndexTypeOfModuleMakesArrayAssociative) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int idx_t;\n"
      "  class key; endclass\n"
      "  localparam int N = 2;\n"
      "  bit [3:0] x;\n"
      "  int at[idx_t];\n"
      "  int ak[key];\n"
      "  int fp[N];\n"
      "  bit [1:0][3:0] pk;\n"
      "  covergroup cg;\n"
      "    a: coverpoint x { bins s[] = at; }\n"
      "    b: coverpoint x { bins s[] = ak; }\n"
      "    c: coverpoint x { bins s[] = fp; }\n"
      "    d: coverpoint x { bins s[] = pk; }\n"
      "  endgroup\n"
      "  cg cv = new;\n"
      "endmodule\n",
      f);
  for (auto [line, name] : {std::pair<uint32_t, const char*>{11u, "at"},
                            std::pair<uint32_t, const char*>{12u, "ak"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("the associative array '") + name +
                                  "' cannot define the bins of a "
                                  "set_covergroup_expression",
                              line, "19.5.1.2"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

// §19.5.1.2: a formal of the covergroup is visible to its set expressions, so
// a formal sharing a bin's name is read, and a formal that is an associative
// array is no more allowed there than a variable that is one.
TEST(CoverpointBinSetExpression, FormalOfCovergroupIsReadAsItsArray) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [3:0] x;\n"
      "  int ma[int];\n"
      "  int md[];\n"
      "  covergroup cg(ref int fa[int], ref int fd[]);\n"
      "    a: coverpoint x { bins fd = {2}; }\n"
      "    b: coverpoint x { bins s[] = fa; }\n"
      "    c: coverpoint x { bins s[] = fd; }\n"
      "  endgroup\n"
      "  cg cv = new(ma, md);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the associative array 'fa' cannot define the "
                            "bins of a set_covergroup_expression",
                            7, "19.5.1.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

// §19.5.1.2 with §7.8: in a class, an index type may be a typedef or a class
// the class declares, a class of the compilation unit, or a typedef of the
// module that declares the class, for a property and a covergroup formal
// alike; and a covergroup of the class reads the module's arrays too.
TEST(CoverpointBinSetExpression, IndexTypeAndArrayOfClassScope) {
  ElabFixture f;
  ElaborateSrc(
      "class key; endclass\n"
      "module m;\n"
      "  typedef int idx_t;\n"
      "  int maa[int];\n"
      "  class k;\n"
      "    typedef byte inner_t;\n"
      "    class nested; endclass\n"
      "    bit [3:0] x;\n"
      "    int ai[inner_t];\n"
      "    int an[nested];\n"
      "    int ak[key];\n"
      "    int am[idx_t];\n"
      "    covergroup cg;\n"
      "      a: coverpoint x { bins s[] = ai; }\n"
      "      b: coverpoint x { bins s[] = an; }\n"
      "      c: coverpoint x { bins s[] = ak; }\n"
      "      d: coverpoint x { bins s[] = am; }\n"
      "      e: coverpoint x { bins s[] = maa; }\n"
      "    endgroup\n"
      "    covergroup cf(ref int fn[nested]);\n"
      "      a: coverpoint x { bins s[] = fn; }\n"
      "    endgroup\n"
      "    function new; cg = new; cf = new(an); endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  for (auto [line, name] : {std::pair<uint32_t, const char*>{14u, "ai"},
                            std::pair<uint32_t, const char*>{15u, "an"},
                            std::pair<uint32_t, const char*>{16u, "ak"},
                            std::pair<uint32_t, const char*>{17u, "am"},
                            std::pair<uint32_t, const char*>{18u, "maa"},
                            std::pair<uint32_t, const char*>{21u, "fn"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("the associative array '") + name +
                                  "' cannot define the bins of a "
                                  "set_covergroup_expression",
                              line, "19.5.1.2"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 6u);
}

}  // namespace
