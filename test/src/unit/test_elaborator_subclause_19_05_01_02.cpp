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

TEST(CoverpointBinSetExpression, ElementTypeAssignmentCompatibleIsAllowed) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kInt;
  DataType element_type;
  element_type.kind = DataTypeKind::kByte;

  EXPECT_TRUE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

TEST(CoverpointBinSetExpression, IncompatibleElementTypeIsRejected) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kInt;
  DataType element_type;
  element_type.kind = DataTypeKind::kString;

  EXPECT_FALSE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

TEST(CoverpointBinSetExpression, RealCoverpointAcceptsRealElement) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kReal;
  DataType element_type;
  element_type.kind = DataTypeKind::kReal;

  EXPECT_TRUE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

TEST(CoverpointBinSetExpression, RealCoverpointRejectsStringElement) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kReal;
  DataType element_type;
  element_type.kind = DataTypeKind::kString;

  EXPECT_FALSE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

TEST(CoverpointBinSetExpression, RealCoverpointAcceptsIntegralElement) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kReal;
  DataType element_type;
  element_type.kind = DataTypeKind::kInt;

  EXPECT_TRUE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

TEST(CoverpointBinSetExpression, IntegralCoverpointAcceptsRealElement) {
  DataType coverpoint_type;
  coverpoint_type.kind = DataTypeKind::kInt;
  DataType element_type;
  element_type.kind = DataTypeKind::kReal;

  EXPECT_TRUE(SetExpressionElementTypeAllowed(coverpoint_type, element_type));
}

TEST(CoverpointBinSetExpression, NonAssociativeArrayKindsAreAllowed) {
  EXPECT_TRUE(
      SetExpressionArrayKindAllowed(SetExpressionArrayKind::kFixedSize));
  EXPECT_TRUE(SetExpressionArrayKindAllowed(SetExpressionArrayKind::kDynamic));
  EXPECT_TRUE(SetExpressionArrayKindAllowed(SetExpressionArrayKind::kQueue));
}

TEST(CoverpointBinSetExpression, AssociativeArrayKindIsRejected) {
  EXPECT_FALSE(
      SetExpressionArrayKindAllowed(SetExpressionArrayKind::kAssociative));
}

TEST(CoverpointBinSetExpression, CovergroupLocalNamesAreNotVisible) {
  EXPECT_FALSE(
      SetExpressionNameVisible(SetExpressionNameOrigin::kCoverpointIdentifier));
  EXPECT_FALSE(
      SetExpressionNameVisible(SetExpressionNameOrigin::kBinIdentifier));
}

TEST(CoverpointBinSetExpression, ExternalNameIsVisible) {
  EXPECT_TRUE(SetExpressionNameVisible(SetExpressionNameOrigin::kExternal));
}

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

TEST(CoverpointBinSetExpression, UndeclaredNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [3:0] x;\n"
      "  int q[] = '{1, 2};\n"
      "  localparam int P = 2;\n"
      "  covergroup cg(int lim);\n"
      "    a: coverpoint x { bins s[] = zz; }\n"
      "    b: coverpoint x { bins s[] = q; }\n"
      "    c: coverpoint x { bins s[] = lim > P ? q : ww; }\n"
      "    d: coverpoint x { bins s[] = b; }\n"
      "  endgroup\n"
      "  cg cv = new(1);\n"
      "endmodule\n",
      f);
  for (auto [line, name] : {std::pair<uint32_t, const char*>{6u, "zz"},
                            std::pair<uint32_t, const char*>{8u, "ww"}}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::string("reference to unresolved identifier '") + name + "'", line,
        "23.9"));
  }
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'b' is declared within covergroup 'cg' and is "
                            "not visible in a set_covergroup_expression",
                            9, "19.5.1.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(CoverpointBinSetExpression, StringElementOfNumericCoverpointIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef enum {A, B} e_t;\n"
      "  bit [3:0] x;\n"
      "  real r;\n"
      "  string sa[] = '{\"a\"};\n"
      "  real ra[] = '{1.0};\n"
      "  byte ba[3];\n"
      "  e_t ea[2];\n"
      "  covergroup cg(ref string fs[]);\n"
      "    a: coverpoint x { bins s[] = sa; }\n"
      "    b: coverpoint x { bins s[] = ra; }\n"
      "    c: coverpoint r { bins s[] = ba; }\n"
      "    d: coverpoint r { bins s[] = sa; }\n"
      "    e: coverpoint x { bins s[] = fs; }\n"
      "    bit [7:0] g: coverpoint x { bins s[] = sa; }\n"
      "    h: coverpoint x { bins s[] = ea; }\n"
      "  endgroup\n"
      "  cg cv = new(sa);\n"
      "endmodule\n",
      f);
  for (auto [line, name] : {std::pair<uint32_t, const char*>{10u, "sa"},
                            std::pair<uint32_t, const char*>{13u, "sa"},
                            std::pair<uint32_t, const char*>{14u, "fs"},
                            std::pair<uint32_t, const char*>{15u, "sa"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("the elements of '") + name +
                                  "' are not assignment compatible with the "
                                  "coverpoint's type",
                              line, "19.5.1.2"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

TEST(CoverpointBinSetExpression, StringElementOfClassCoverpointIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class k;\n"
      "    bit [3:0] x;\n"
      "    string sa[];\n"
      "    int ia[];\n"
      "    covergroup cg;\n"
      "      a: coverpoint x { bins s[] = sa; }\n"
      "      b: coverpoint x { bins s[] = ia; }\n"
      "    endgroup\n"
      "    function new; cg = new; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the elements of 'sa' are not assignment "
                            "compatible with the coverpoint's type",
                            7, "19.5.1.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(CoverpointBinSetExpression, UndeclaredNameInClassCovergroupIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int mq[] = '{1};\n"
      "  class k;\n"
      "    bit [3:0] x;\n"
      "    int ia[];\n"
      "    covergroup cg;\n"
      "      a: coverpoint x { bins s[] = zz; }\n"
      "      b: coverpoint x { bins s[] = ia; }\n"
      "      c: coverpoint x { bins s[] = mq; }\n"
      "    endgroup\n"
      "    function new; cg = new; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'zz'", 7,
                            "23.9"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
