#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_config_params.h"
#include "helpers_param_value_assignability.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ParamValueAssignability, EnumParameterGivenAValueOfAnotherTypeIsReported) {
  const IncompatibleValue kCases[] = {
      {"an integer literal",
       "module m;\n  typedef enum {A, B} e_t;\n  parameter e_t E = 1;\n"
       "endmodule\n",
       "E", 3},
      {"a real literal",
       "module m;\n  typedef enum {A, B} e_t;\n  parameter e_t E = 1.0;\n"
       "endmodule\n",
       "E", 3},
      {"an unbased unsized literal",
       "module m;\n  typedef enum {A, B} e_t;\n  parameter e_t E = '0;\n"
       "endmodule\n",
       "E", 3},
      {"a negated constant of its type",
       "module m;\n  typedef enum {A, B} e_t;\n  parameter e_t E = -B;\n"
       "endmodule\n",
       "E", 3},
      {"a sum with a constant of its type",
       "module m;\n  typedef enum {A, B} e_t;\n  parameter e_t E = A + 1;\n"
       "endmodule\n",
       "E", 3},
      {"a constant of another enumeration",
       "module m;\n  typedef enum {A, B} e_t;\n  typedef enum {X, Y} f_t;\n"
       "  parameter e_t E = X;\nendmodule\n",
       "E", 4},
      {"an int parameter",
       "module m;\n  typedef enum {A, B} e_t;\n  parameter int I = 1;\n"
       "  parameter e_t E = I;\nendmodule\n",
       "E", 4},
      {"a parameter of another enumeration",
       "module m;\n  typedef enum {A, B} e_t;\n  typedef enum {X, Y} f_t;\n"
       "  parameter f_t F = X;\n  parameter e_t E = F;\nendmodule\n",
       "E", 5},
      {"a size cast",
       "module m;\n  typedef enum {A, B} e_t;\n  parameter e_t E = 8'(B);\n"
       "endmodule\n",
       "E", 3},
      {"a size cast written as a parameter's name",
       "module m;\n  typedef enum {A, B} e_t;\n  parameter int W = 8;\n"
       "  parameter e_t E = W'(B);\nendmodule\n",
       "E", 4},
      {"an int cast",
       "module m;\n  typedef enum {A, B} e_t;\n  parameter e_t E = int'(B);\n"
       "endmodule\n",
       "E", 3},
      {"a const cast of an integer",
       "module m;\n  typedef enum {A, B} e_t;\n"
       "  parameter e_t E = const'(1);\nendmodule\n",
       "E", 3},
      {"a conditional choosing between two enumerations",
       "module m;\n  typedef enum {A, B} e_t;\n  typedef enum {X, Y} f_t;\n"
       "  parameter bit C = 1;\n  parameter e_t E = C ? A : X;\nendmodule\n",
       "E", 5},
      {"a conditional choosing between an integer and a constant",
       "module m;\n  typedef enum {A, B} e_t;\n  parameter bit C = 1;\n"
       "  parameter e_t E = C ? 1 : A;\nendmodule\n",
       "E", 4},
      {"a package constant of another enumeration",
       "package p;\n  typedef enum {P0, P1} p_t;\nendpackage\nmodule m;\n"
       "  typedef enum {A, B} e_t;\n  parameter e_t E = p::P1;\nendmodule\n",
       "E", 6},
      {"a cast to a package enumeration",
       "package p;\n  typedef enum {P0, P1} p_t;\nendpackage\nmodule m;\n"
       "  typedef enum {A, B} e_t;\n  parameter e_t E = p::p_t'(1);\n"
       "endmodule\n",
       "E", 6},
      {"an integer for a package enumeration",
       "package p;\n  typedef enum {P0, P1} p_t;\nendpackage\nmodule m;\n"
       "  parameter p::p_t E = 1;\nendmodule\n",
       "E", 5},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability, EnumParameterGivenAValueOfItsTypeIsAccepted) {
  const char* const kSources[] = {
      "module m;\n  typedef enum {A, B} e_t;\n  parameter e_t E = B;\n"
      "endmodule\n",
      "module m;\n  typedef enum {A, B} e_t;\n  parameter e_t E = e_t'(1);\n"
      "endmodule\n",
      "module m;\n  typedef enum {A, B} e_t;\n  parameter e_t E = const'(B);\n"
      "endmodule\n",
      "module m;\n  typedef enum {A, B} e_t;\n  parameter e_t E = B;\n"
      "  parameter e_t F = E;\nendmodule\n",
      "module m;\n  typedef enum {A, B} e_t;\n  parameter bit C = 1;\n"
      "  parameter e_t E = C ? A : B;\nendmodule\n",
      "module m;\n  typedef enum {A, B} e_t;\n  parameter int I = B;\n"
      "  parameter bit C = 1;\n  parameter int J = C ? 1 : A;\nendmodule\n",
      "package p;\n  typedef enum {P0, P1} p_t;\nendpackage\nmodule m;\n"
      "  parameter p::p_t E = p::P1;\n  parameter p::p_t F = p::p_t'(1);\n"
      "endmodule\n",
      "package p;\n  typedef enum {A, B} p_t;\nendpackage\nmodule m;\n"
      "  typedef enum {B, C} f_t;\n  parameter f_t F = B;\nendmodule\n",
  };
  ExpectEachAccepted(kSources);
}

TEST(ParamValueAssignability, StringParameterGivenAnIntegralValueIsReported) {
  const IncompatibleValue kCases[] = {
      {"an integer literal",
       "module m;\n  parameter string S = 65;\nendmodule\n", "S", 2},
      {"a time literal", "module m;\n  parameter string S = 1ns;\nendmodule\n",
       "S", 2},
      {"an int parameter",
       "module m;\n  parameter int I = 1;\n  parameter string S = I;\n"
       "endmodule\n",
       "S", 3},
      {"an untyped parameter holding an integer",
       "module m;\n  parameter X = 1;\n  parameter string S = X;\n"
       "endmodule\n",
       "S", 3},
      {"a concatenation of integral values",
       "module m;\n  parameter int I = 1;\n"
       "  parameter string S = {I, 8'd1};\nendmodule\n",
       "S", 3},
      {"a string parameter for an int",
       "module m;\n  parameter string S = \"a\";\n  parameter int I = S;\n"
       "endmodule\n",
       "I", 3},
      {"a string cast for an int",
       "module m;\n  parameter int I = string'(\"a\");\nendmodule\n", "I", 2},
      {"a concatenation holding a string for an int",
       "module m;\n  parameter string S = \"a\";\n"
       "  parameter int I = {S, \"b\"};\nendmodule\n",
       "I", 3},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability, StringParameterGivenAStringValueIsAccepted) {
  const char* const kSources[] = {
      "module m;\n  parameter string S = \"A\";\nendmodule\n",
      "module m;\n  parameter string S0 = \"a\";\n"
      "  parameter string S = S0;\nendmodule\n",
      "module m;\n  parameter string S0 = \"a\";\n"
      "  parameter string S = {S0, \"c\"};\nendmodule\n",
      "module m;\n  parameter string S = {\"a\", \"b\"};\nendmodule\n",
      "module m;\n  parameter string S = {2{\"ab\"}};\nendmodule\n",
      "module m;\n  parameter string S = string'(65);\nendmodule\n",
      "module m;\n  parameter int I = \"A\";\nendmodule\n",
      "module m;\n  parameter bit C = 1;\n  parameter string S0 = \"a\";\n"
      "  parameter string S = C ? S0 : \"b\";\nendmodule\n",
      "module m;\n  parameter bit C = 1;\n  parameter string S0 = \"a\";\n"
      "  parameter string S = C ? \"b\" : S0;\nendmodule\n",
      "parameter string P = \"a\";\nmodule m;\n  parameter int P = 1;\n"
      "  parameter string S = $unit::P;\nendmodule\n",
      "module m;\n  parameter realtime T = 1ns;\n  parameter int Z = '0;\n"
      "  parameter X = 1;\n  parameter int I = X;\nendmodule\n",
  };
  ExpectEachAccepted(kSources);
}

TEST(ParamValueAssignability, ClassParameterGivenAnUnrelatedValueIsReported) {
  const IncompatibleValue kCases[] = {
      {"an integer literal",
       "class K;\nendclass\nmodule m;\n  parameter K H = 5;\nendmodule\n", "H",
       4},
      {"a handle of an unrelated class",
       "class K;\nendclass\nclass J;\nendclass\nmodule m;\n"
       "  parameter J G = null;\n  parameter K H = G;\nendmodule\n",
       "H", 7},
      {"a handle of its base class",
       "class K;\nendclass\nclass L extends K;\nendclass\nmodule m;\n"
       "  parameter K H = null;\n  parameter L D = H;\nendmodule\n",
       "D", 7},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability,
     ClassParameterGivenNullOrARelatedHandleIsAccepted) {
  const char* const kSources[] = {
      "class K;\nendclass\nmodule m;\n  parameter K H = null;\n"
      "  parameter K H2 = H;\nendmodule\n",
      "class K;\nendclass\nclass L extends K;\nendclass\nmodule m;\n"
      "  parameter L D = null;\n  parameter K H = D;\nendmodule\n",
  };
  ExpectEachAccepted(kSources);
}

TEST(ParamValueAssignability, ArrayParameterGivenAnUnequalArrayIsReported) {
  const IncompatibleValue kCases[] = {
      {"an array of another size",
       "module m;\n  parameter int A[2] = '{1, 2};\n"
       "  parameter int B[3] = A;\nendmodule\n",
       "B", 3},
      {"an array of another size given by a parameter",
       "module m;\n  parameter int A[2] = '{1, 2};\n  parameter int N = 3;\n"
       "  parameter int B[N] = A;\nendmodule\n",
       "B", 4},
      {"an array of more dimensions",
       "module m;\n  parameter int D[2][2] = '{'{1, 2}, '{3, 4}};\n"
       "  parameter int B[2] = D;\nendmodule\n",
       "B", 3},
      {"an array of another element type",
       "module m;\n  parameter int A[2] = '{1, 2};\n"
       "  parameter byte B[2] = A;\nendmodule\n",
       "B", 3},
      {"an array for a typedef of another element type",
       "module m;\n  typedef byte b2_t[2];\n  parameter int A[2] = '{1, 2};\n"
       "  parameter b2_t B = A;\nendmodule\n",
       "B", 4},
      {"a typed pattern of another element type",
       "module m;\n  typedef byte b2_t[2];\n"
       "  parameter int B[2] = b2_t'{1, 2};\nendmodule\n",
       "B", 3},
      {"an integer", "module m;\n  parameter int B[2] = 5;\nendmodule\n", "B",
       2},
      {"an array for an int",
       "module m;\n  parameter int A[2] = '{1, 2};\n"
       "  parameter int I = A;\nendmodule\n",
       "I", 3},
      {"an array of handles of an unrelated class",
       "class K;\nendclass\nclass J;\nendclass\nmodule m;\n"
       "  parameter K KA[2] = '{null, null};\n  parameter J JB[2] = KA;\n"
       "endmodule\n",
       "JB", 7},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability, ArrayParameterGivenAnEqualArrayIsAccepted) {
  const char* const kSources[] = {
      "module m;\n  parameter int A[2] = '{1, 2};\n"
      "  parameter int B[2] = A;\n  parameter int C[2] = '{3, 4};\n"
      "  parameter int N = 2;\n  parameter int D[N] = A;\n"
      "  parameter int E = A[1];\nendmodule\n",
      "module m;\n  typedef int i2_t[2];\n  parameter int A[2] = '{1, 2};\n"
      "  parameter i2_t B = A;\n  parameter int C[2] = i2_t'{1, 2};\n"
      "endmodule\n",
      "class K;\nendclass\nmodule m;\n"
      "  parameter K KA[2] = '{null, null};\n  parameter K KB[2] = KA;\n"
      "endmodule\n",
      ("class C #(int N = 2, int A[N] = '{1, 2}, int B[2] = A,\n"
       "          int D[N] = B);\nendclass\nmodule m;\nendmodule\n"),
  };
  ExpectEachAccepted(kSources);
}

TEST(ParamValueAssignability, StructureParameterGivenAnotherTypeIsReported) {
  const IncompatibleValue kCases[] = {
      {"a parameter of another structure",
       "module m;\n  typedef struct { int a; int b; } s_t;\n"
       "  typedef struct { int a; int b; } t_t;\n"
       "  parameter s_t S = '{1, 2};\n  parameter t_t T = S;\nendmodule\n",
       "T", 5},
      {"a typed pattern of another structure",
       "module m;\n  typedef struct { int a; int b; } s_t;\n"
       "  typedef struct { int a; int b; } t_t;\n"
       "  parameter t_t T = s_t'{1, 2};\nendmodule\n",
       "T", 4},
      {"an integer",
       "module m;\n  typedef struct { int a; int b; } s_t;\n"
       "  parameter s_t S = 5;\nendmodule\n",
       "S", 3},
      {"an integer for an unpacked union",
       "module m;\n  typedef union { int a; byte b; } u_t;\n"
       "  parameter u_t U = 5;\nendmodule\n",
       "U", 3},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability, StructureParameterGivenItsTypeIsAccepted) {
  const char* const kSources[] = {
      "module m;\n  typedef struct { int a; int b; } s_t;\n"
      "  parameter s_t S = '{1, 2};\n  parameter s_t S2 = S;\n"
      "  parameter s_t S3 = s_t'{a: 3, b: 4};\n  parameter int I = S.a;\n"
      "endmodule\n",
      "module m;\n  typedef struct packed { int a; int b; } p_t;\n"
      "  typedef union packed { int a; int b; } q_t;\n"
      "  parameter p_t P = 5;\n  parameter p_t P2 = '{a: 1, b: 2};\n"
      "  parameter q_t Q = 5;\n  parameter int L = $clog2(4);\nendmodule\n",
  };
  ExpectEachAccepted(kSources);
}

TEST(ParamValueAssignability, EnumValueOfAnotherTypeIsReportedInEveryPlace) {
  const IncompatibleValue kCases[] = {
      {"module body parameter",
       "typedef enum {A, B} e_t;\nmodule m;\n  parameter e_t E = 1;\n"
       "endmodule\n",
       "E", 3},
      {"module body localparam",
       "typedef enum {A, B} e_t;\nmodule m;\n  localparam e_t E = 1;\n"
       "endmodule\n",
       "E", 3},
      {"module port list parameter",
       "typedef enum {A, B} e_t;\nmodule m #(parameter e_t E = 1);\n"
       "endmodule\n",
       "E", 2},
      {"module port list localparam",
       "typedef enum {A, B} e_t;\nmodule m #(localparam e_t E = 1);\n"
       "endmodule\n",
       "E", 2},
      {"interface body parameter",
       "typedef enum {A, B} e_t;\ninterface i;\n  parameter e_t E = 1;\n"
       "endinterface\nmodule m;\n  i u();\nendmodule\n",
       "E", 3},
      {"interface port list parameter",
       "typedef enum {A, B} e_t;\ninterface i #(parameter e_t E = 1);\n"
       "endinterface\nmodule m;\n  i u();\nendmodule\n",
       "E", 2},
      {"program body parameter",
       "typedef enum {A, B} e_t;\nprogram p;\n  parameter e_t E = 1;\n"
       "endprogram\nmodule m;\n  p u();\nendmodule\n",
       "E", 3},
      {"program port list parameter",
       "typedef enum {A, B} e_t;\nprogram p #(parameter e_t E = 1);\n"
       "endprogram\nmodule m;\n  p u();\nendmodule\n",
       "E", 2},
      {"generate block parameter",
       "typedef enum {A, B} e_t;\nmodule m;\n  if (1) begin : g\n"
       "    parameter e_t E = 1;\n  end\nendmodule\n",
       "E", 4},
      {"package parameter",
       "package p;\n  typedef enum {A, B} e_t;\n  parameter e_t E = 1;\n"
       "endpackage\nmodule m;\nendmodule\n",
       "E", 3},
      {"compilation-unit parameter",
       "typedef enum {A, B} e_t;\nparameter e_t E = 1;\nmodule m;\n"
       "endmodule\n",
       "E", 2},
      {"class port list parameter",
       "typedef enum {A, B} e_t;\nclass C #(e_t E = 1);\nendclass\n"
       "module m;\nendmodule\n",
       "E", 2},
      {"class body parameter beside a property and a method",
       "typedef enum {A, B} e_t;\nclass C;\n  int x;\n"
       "  function void f();\n  endfunction\n  parameter e_t E = 1;\n"
       "endclass\nmodule m;\nendmodule\n",
       "E", 6},
      {"port list parameter of a class declared in a module",
       "typedef enum {A, B} e_t;\nmodule m;\n  class C #(e_t E = 1);\n"
       "  endclass\nendmodule\n",
       "E", 3},
      {"port list parameter of a class declared in a package",
       "package p;\n  typedef enum {A, B} e_t;\n  class C #(e_t E = 1);\n"
       "  endclass\nendpackage\nmodule m;\nendmodule\n",
       "E", 3},
      {"body parameter of a class declared in a package",
       "package p;\n  typedef enum {A, B} e_t;\n  class C;\n"
       "    parameter e_t E = 1;\n  endclass\nendpackage\nmodule m;\n"
       "endmodule\n",
       "E", 4},
      {"function parameter in a module",
       "typedef enum {A, B} e_t;\nmodule m;\n  function int f();\n"
       "    int x;\n    parameter e_t E = 1;\n    return x;\n  endfunction\n"
       "endmodule\n",
       "E", 5},
      {"task parameter in a module",
       "typedef enum {A, B} e_t;\nmodule m;\n  task t();\n    int x;\n"
       "    parameter e_t E = 1;\n  endtask\nendmodule\n",
       "E", 5},
      {"named block parameter in an initial procedure",
       "typedef enum {A, B} e_t;\nmodule m;\n  initial begin : b\n"
       "    int x;\n    parameter e_t E = 1;\n  end\nendmodule\n",
       "E", 5},
      {"function parameter in a package",
       "package p;\n  typedef enum {A, B} e_t;\n"
       "  function automatic int f();\n    parameter e_t E = 1;\n"
       "    return 0;\n  endfunction\nendpackage\nmodule m;\nendmodule\n",
       "E", 4},
      {"function parameter in the compilation unit",
       "typedef enum {A, B} e_t;\nfunction automatic int f();\n"
       "  parameter e_t E = 1;\n  return 0;\nendfunction\nmodule m;\n"
       "endmodule\n",
       "E", 3},
      {"method parameter in a class",
       "typedef enum {A, B} e_t;\nclass C;\n  function int f();\n"
       "    parameter e_t E = 1;\n    return 0;\n  endfunction\nendclass\n"
       "module m;\nendmodule\n",
       "E", 4},
      {"named block parameter in a final procedure",
       "typedef enum {A, B} e_t;\nmodule m;\n  final begin : b\n"
       "    parameter e_t E = 1;\n  end\nendmodule\n",
       "E", 4},
      {"named block parameter in an initial procedure of a generate block",
       "typedef enum {A, B} e_t;\nmodule m;\n  if (1) begin : g\n"
       "    initial begin : b\n      parameter e_t E = 1;\n    end\n  end\n"
       "endmodule\n",
       "E", 5},
      {"generate block parameter of a type the block declares",
       "module m;\n  if (1) begin : g\n    typedef enum {X, Y} f_t;\n"
       "    parameter f_t F = 1;\n  end\nendmodule\n",
       "F", 4},
      {"generate block parameter naming the block's own parameter",
       "module m;\n  parameter string S = \"a\";\n  if (1) begin : g\n"
       "    parameter int S = 1;\n    parameter string J = S;\n  end\n"
       "endmodule\n",
       "J", 5},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability, DefaultIsReportedInAnInstanceAfterOneOfNoModule) {
  ElabFixture f;
  ElaborateSrc(
      "typedef enum {A, B} e_t;\nmodule c;\n  parameter e_t E = 1;\n"
      "endmodule\nmodule t;\n  missing m();\n  c u();\nendmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), NotAssignable("E"), 3, "6.20.2"));
}

TEST(ParamValueAssignability,
     ParameterOfAGenerateBlockNotElaboratedIsNotJudged) {
  ElabFixture f;
  ElaborateSrc(
      "typedef enum {A, B} e_t;\nmodule m;\n  if (0) begin : g\n"
      "    parameter e_t E = 1;\n  end\nendmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(ParamValueAssignability, EnumValueOfItsTypeIsAcceptedInEveryPlace) {
  const char* const kSources[] = {
      "typedef enum {A, B} e_t;\nmodule m #(parameter e_t E = B,\n"
      "           localparam e_t L = A);\n  parameter e_t F = B;\n"
      "  localparam e_t G = E;\n  if (1) begin : g\n"
      "    parameter e_t H = B;\n  end\nendmodule\n",
      "typedef enum {A, B} e_t;\ninterface i #(parameter e_t E = B);\n"
      "  parameter e_t F = E;\nendinterface\nprogram p #(parameter e_t E = "
      "B);\n"
      "  parameter e_t F = E;\nendprogram\nmodule m;\n  i u();\n  p v();\n"
      "endmodule\n",
      "package p;\n  typedef enum {A, B} e_t;\n  parameter e_t E = B;\n"
      "  parameter e_t F = E;\n  class C #(e_t P = B);\n"
      "    parameter e_t Q = P;\n  endclass\nendpackage\nmodule m;\n"
      "endmodule\n",
      "typedef enum {A, B} e_t;\nparameter e_t E = B;\nparameter e_t F = E;\n"
      "parameter string G = \"g\";\nclass C #(e_t P = B, int N = 1);\n"
      "  int x;\n  parameter e_t Q = P;\n  parameter e_t R = Q;\n"
      "  parameter e_t S = F;\n  function int f();\n"
      "    parameter e_t T = B;\n    return 0;\n  endfunction\nendclass\n"
      "module m;\nendmodule\n",
      "typedef enum {A, B} e_t;\nmodule m;\n  function int f();\n"
      "    int x;\n    parameter e_t E = B;\n    if (1) begin\n"
      "      parameter e_t F = A;\n    end\n    return x;\n  endfunction\n"
      "  task t();\n    parameter e_t E = B;\n  endtask\n"
      "  initial begin : b\n    int x;\n    parameter e_t E = B;\n  end\n"
      "endmodule\n",
      "typedef enum {A, B} e_t;\nmodule m;\n  final begin : b\n"
      "    parameter e_t E = B;\n  end\n  if (1) begin : g\n"
      "    typedef enum {X, Y} f_t;\n    parameter f_t F = Y;\n"
      "    initial begin : b\n      parameter e_t E = B;\n    end\n  end\n"
      "endmodule\n",
      "module m;\n  parameter string S = \"a\";\n  if (1) begin : g\n"
      "    parameter int S = 1;\n    parameter int J = S;\n  end\n"
      "endmodule\n",
      "module m;\n  if (1) begin : g1\n    parameter string S = \"a\";\n"
      "  end\n  if (1) begin : g2\n    parameter int S = 1;\n"
      "    parameter int J = S;\n  end\nendmodule\n",
  };
  ExpectEachAccepted(kSources);
}

TEST(ParamValueAssignability, ClassParameterReferencesResolveInItsScopes) {
  const IncompatibleValue kCases[] = {
      {"a body parameter naming another body parameter",
       "class C #(int N = 1);\n  int x;\n  parameter int L = 1;\n"
       "  parameter string S = L;\nendclass\nmodule m;\nendmodule\n",
       "S", 4},
      {"a body parameter naming a compilation-unit parameter",
       "parameter string G = \"g\";\nclass C;\n  parameter int I = G;\n"
       "endclass\nmodule m;\nendmodule\n",
       "I", 3},
      {"a port list parameter naming an earlier one",
       "class C #(int N = 1, string S = N);\nendclass\nmodule m;\n"
       "endmodule\n",
       "S", 1},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability, OverrideOfAnotherTypeIsReportedAtTheOverride) {
  const IncompatibleValue kCases[] = {
      {"a named instance override of a port list parameter",
       "typedef enum {A, B} e_t;\nmodule c #(parameter e_t E = A);\n"
       "endmodule\nmodule t;\n  c #(.E(1)) u();\nendmodule\n",
       "E", 5},
      {"an ordered instance override of a port list parameter",
       "typedef enum {A, B} e_t;\nmodule c #(parameter e_t E = A);\n"
       "endmodule\nmodule t;\n  c #(1) u();\nendmodule\n",
       "E", 5},
      {"an instance override of a body parameter",
       "typedef enum {A, B} e_t;\nmodule c;\n  parameter e_t E = A;\n"
       "endmodule\nmodule t;\n  c #(.E(1)) u();\nendmodule\n",
       "E", 6},
      {"an interface instance override",
       "typedef enum {A, B} e_t;\ninterface i #(parameter e_t E = A);\n"
       "endinterface\nmodule t;\n  i #(.E(1)) u();\nendmodule\n",
       "E", 5},
      {"an instance override naming a parameter of the instantiating module",
       "module c #(parameter string S = \"a\");\nendmodule\nmodule t;\n"
       "  parameter int W = 1;\n  c #(.S(W)) u();\nendmodule\n",
       "S", 5},
      {"an instance override naming an untyped parameter of the "
       "instantiating module",
       "module c #(parameter string S = \"a\");\nendmodule\nmodule t;\n"
       "  parameter W = 1;\n  c #(.S(W)) u();\nendmodule\n",
       "S", 5},
      {"a defparam",
       "typedef enum {A, B} e_t;\nmodule c;\n  parameter e_t E = A;\n"
       "endmodule\nmodule t;\n  c u();\n  defparam u.E = 1;\nendmodule\n",
       "E", 7},
      {"a defparam naming an array of another size",
       "module c;\n  parameter int P[2] = '{1, 2};\nendmodule\nmodule t;\n"
       "  parameter int Q[3] = '{1, 2, 3};\n  c u();\n  defparam u.P = Q;\n"
       "endmodule\n",
       "P", 7},
      {"the default of a parameter whose type parameter is overridden",
       "module c #(type T = int, parameter T V = 0);\nendmodule\n"
       "module t;\n  c #(.T(string)) u();\nendmodule\n",
       "V", 1},
      {"a named class specialization in a variable declaration",
       "typedef enum {A, B} e_t;\nclass C #(e_t E = A);\nendclass\n"
       "module m;\n  C #(.E(1)) h;\nendmodule\n",
       "E", 5},
      {"an ordered class specialization in a variable declaration",
       "typedef enum {A, B} e_t;\nclass C #(e_t E = A);\nendclass\n"
       "module m;\n  C #(1) h;\nendmodule\n",
       "E", 5},
      {"a specialization of a class imported from a package",
       "package p;\n  typedef enum {A, B} e_t;\n  class C #(e_t E = A);\n"
       "  endclass\nendpackage\nmodule m;\n  import p::*;\n  C #(1) h;\n"
       "endmodule\n",
       "E", 8},
      {"a specialization in an extends clause",
       "typedef enum {A, B} e_t;\nclass C #(e_t E = A);\nendclass\n"
       "class D extends C #(1);\nendclass\nmodule m;\nendmodule\n",
       "E", 4},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability, OverrideOfItsTypeIsAccepted) {
  const char* const kSources[] = {
      "typedef enum {A, B} e_t;\nmodule c #(parameter e_t E = A);\n"
      "  parameter e_t F = A;\nendmodule\nmodule t;\n  c #(.E(B)) u();\n"
      "  c #(B) v();\nendmodule\n",
      "typedef enum {A, B} e_t;\nmodule c;\n  parameter e_t E = A;\n"
      "endmodule\nmodule t;\n  c #(.E(B)) u();\n  c v();\n"
      "  defparam v.E = B;\nendmodule\n",
      "module c #(parameter string S = \"a\");\nendmodule\nmodule t;\n"
      "  parameter string W = \"w\";\n  c #(.S(W)) u();\nendmodule\n",
      "module c;\n  parameter int P[2] = '{1, 2};\nendmodule\nmodule t;\n"
      "  c u();\n  defparam u.P = '{3, 4};\nendmodule\n",
      "module c #(type T = int, parameter T V = 0);\nendmodule\n"
      "module t;\n  c #(.T(string), .V(\"a\")) u();\nendmodule\n",
      "module c #(parameter P, parameter int Q = P);\nendmodule\n"
      "module t;\n  c #(.P(1)) u();\nendmodule\n",
      "typedef enum {A, B} e_t;\nclass C #(e_t E = A);\nendclass\n"
      "class D extends C #(B);\nendclass\nclass F extends C;\nendclass\n"
      "module m;\n  C #(.E(B)) h;\n  C #(A) g;\n  C k;\nendmodule\n",
      "module c #(parameter X = 1, parameter string S = X);\nendmodule\n"
      "module t;\n  c #(.X(\"a\")) u();\nendmodule\n",
      "typedef enum {A, B} e_t;\nmodule c;\n  parameter X = 0;\n"
      "  parameter e_t E = X;\nendmodule\nmodule t;\n  c u();\n"
      "  defparam u.X = B;\nendmodule\n",
      "typedef enum {A, B} e_t;\nmodule c #(parameter e_t E = 1);\n"
      "endmodule\nmodule t;\n  c #(.E(B)) u();\nendmodule\n",
      "typedef enum {A, B} e_t;\nmodule c;\n  parameter e_t E = 1;\n"
      "endmodule\nmodule t;\n  c u();\n  defparam u.E = B;\nendmodule\n",
  };
  ExpectEachAccepted(kSources);
}

TEST(ParamValueAssignability, ConfigurationOverrideOfAnotherTypeIsReported) {
  const IncompatibleValue kCases[] = {
      {"an instance clause on the top cell",
       "typedef enum {A, B} e_t;\nmodule top #(parameter e_t E = A);\n"
       "endmodule\nconfig cfg1;\n  design top;\n"
       "  instance top use #(.E(1));\nendconfig\n",
       "E", 6},
      {"an instance clause on a child instance",
       "typedef enum {A, B} e_t;\nmodule c #(parameter e_t E = A);\n"
       "endmodule\nmodule top;\n  c u();\nendmodule\nconfig cfg1;\n"
       "  design top;\n  instance top.u use #(.E(1));\nendconfig\n",
       "E", 9},
  };
  for (const IncompatibleValue& value : kCases) {
    SCOPED_TRACE(value.where);
    ElabFixture f;
    ConfigElab(f, value.src);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), NotAssignable(value.param),
                              value.line, "6.20.2"));
  }
}

TEST(ParamValueAssignability, ConfigurationOverrideOfItsTypeIsAccepted) {
  ElabFixture f;
  ConfigElab(f,
             "typedef enum {A, B} e_t;\nmodule c #(parameter e_t E = A);\n"
             "endmodule\nmodule top #(parameter e_t E = A);\n  c u();\n"
             "endmodule\nconfig cfg1;\n  design top;\n"
             "  instance top use #(.E(B));\n  instance top.u use #(.E(B));\n"
             "endconfig\n");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
