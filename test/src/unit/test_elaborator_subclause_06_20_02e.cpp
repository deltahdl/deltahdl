#include <gtest/gtest.h>

#include "helpers_param_value_assignability.h"

using namespace delta;

namespace {

TEST(ParamValueAssignability, InPlaceEnumConstantIsReportedInEveryPlace) {
  const IncompatibleValue kCases[] = {
      {"a constant of a module variable's enumeration",
       "typedef enum {A, B} e_t;\nmodule m;\n  enum {X, Y} v;\n"
       "  parameter e_t E = Y;\nendmodule\n",
       "E", 4},
      {"a constant of a module net's enumeration",
       "typedef enum {A, B} e_t;\nmodule m;\n  wire enum logic {X, Y} w;\n"
       "  parameter e_t E = Y;\nendmodule\n",
       "E", 4},
      {"a constant of a module parameter's enumeration",
       "typedef enum {A, B} e_t;\nmodule m;\n  parameter enum {X, Y} F = X;\n"
       "  parameter e_t E = Y;\nendmodule\n",
       "E", 4},
      {"a constant of a module structure member's enumeration",
       "typedef enum {A, B} e_t;\nmodule m;\n  struct {enum {X, Y} f;} s;\n"
       "  parameter e_t E = Y;\nendmodule\n",
       "E", 4},
      {"a constant of a module port list parameter's enumeration",
       "typedef enum {A, B} e_t;\n"
       "module m #(parameter enum {X, Y} F = X, parameter e_t E = Y);\n"
       "endmodule\n",
       "E", 2},
      {"a constant of another in-place enumeration for an in-place one",
       "module m;\n  enum {X, Y} v;\n  parameter enum {P, Q} E = X;\n"
       "endmodule\n",
       "E", 3},
      {"a constant named by a range",
       "typedef enum {A, B} e_t;\nmodule m;\n  enum {X[2]} v;\n"
       "  parameter e_t E = X1;\nendmodule\n",
       "E", 4},
      {"a module localparam",
       "typedef enum {A, B} e_t;\nmodule m;\n  enum {X, Y} v;\n"
       "  localparam e_t E = Y;\nendmodule\n",
       "E", 4},
      {"an interface",
       "typedef enum {A, B} e_t;\ninterface i;\n  enum {X, Y} v;\n"
       "  parameter e_t E = Y;\nendinterface\nmodule m;\n  i u();\n"
       "endmodule\n",
       "E", 4},
      {"a program",
       "typedef enum {A, B} e_t;\nprogram p;\n  enum {X, Y} v;\n"
       "  parameter e_t E = Y;\nendprogram\nmodule m;\n  p u();\nendmodule\n",
       "E", 4},
      {"a generate block",
       "typedef enum {A, B} e_t;\nmodule m;\n  if (1) begin : g\n"
       "    enum {X, Y} v;\n    parameter e_t E = Y;\n  end\nendmodule\n",
       "E", 5},
      {"a generate block net",
       "typedef enum {A, B} e_t;\nmodule m;\n  if (1) begin : g\n"
       "    wire enum logic {X, Y} w;\n    parameter e_t E = Y;\n  end\n"
       "endmodule\n",
       "E", 5},
      {"a generate block reading its module's constant",
       "typedef enum {A, B} e_t;\nmodule m;\n  enum {X, Y} v;\n"
       "  if (1) begin : g\n    parameter e_t E = Y;\n  end\nendmodule\n",
       "E", 5},
      {"a package variable",
       "package p;\n  typedef enum {A, B} e_t;\n  enum {X, Y} v;\n"
       "  parameter e_t E = Y;\nendpackage\nmodule m;\nendmodule\n",
       "E", 4},
      {"a package parameter",
       "package p;\n  typedef enum {A, B} e_t;\n"
       "  parameter enum {X, Y} F = X;\n  parameter e_t E = Y;\n"
       "endpackage\nmodule m;\nendmodule\n",
       "E", 4},
      {"a package structure member",
       "package p;\n  typedef enum {A, B} e_t;\n  struct {enum {X, Y} f;} s;\n"
       "  parameter e_t E = Y;\nendpackage\nmodule m;\nendmodule\n",
       "E", 4},
      {"a package constant named by a range",
       "package p;\n  typedef enum {A, B} e_t;\n  enum {X[2]} v;\n"
       "  parameter e_t E = X1;\nendpackage\nmodule m;\nendmodule\n",
       "E", 4},
      {"a compilation-unit variable",
       "typedef enum {A, B} e_t;\nenum {X, Y} v;\nparameter e_t E = Y;\n"
       "module m;\nendmodule\n",
       "E", 3},
      {"a compilation-unit parameter",
       "typedef enum {A, B} e_t;\nparameter enum {X, Y} F = X;\n"
       "parameter e_t E = Y;\nmodule m;\nendmodule\n",
       "E", 3},
      {"a compilation-unit structure member",
       "typedef enum {A, B} e_t;\nstruct {enum {X, Y} f;} s;\n"
       "parameter e_t E = Y;\nmodule m;\nendmodule\n",
       "E", 3},
      {"a class property",
       "typedef enum {A, B} e_t;\nclass C;\n  enum {X, Y} v;\n"
       "  parameter e_t E = Y;\nendclass\nmodule m;\nendmodule\n",
       "E", 4},
      {"a class port list parameter",
       "typedef enum {A, B} e_t;\nclass C #(enum {X, Y} F = X, e_t E = Y);\n"
       "endclass\nmodule m;\nendmodule\n",
       "E", 2},
      {"a class typedef",
       "typedef enum {A, B} e_t;\nclass C;\n  typedef enum {X, Y} f_t;\n"
       "  parameter e_t E = Y;\nendclass\nmodule m;\nendmodule\n",
       "E", 4},
      {"a class body parameter",
       "typedef enum {A, B} e_t;\nclass C;\n  parameter enum {X, Y} F = X;\n"
       "  parameter e_t E = Y;\nendclass\nmodule m;\nendmodule\n",
       "E", 4},
      {"a class structure property",
       "typedef enum {A, B} e_t;\nclass C;\n  struct {enum {X, Y} f;} s;\n"
       "  parameter e_t E = Y;\nendclass\nmodule m;\nendmodule\n",
       "E", 4},
      {"a class constant named by a range",
       "typedef enum {A, B} e_t;\nclass C;\n  enum {X[2]} v;\n"
       "  parameter e_t E = X1;\nendclass\nmodule m;\nendmodule\n",
       "E", 4},
      {"a class in a module reading the module's constant",
       "typedef enum {A, B} e_t;\nmodule m;\n  enum {X, Y} v;\n  class C;\n"
       "    parameter e_t E = Y;\n  endclass\nendmodule\n",
       "E", 5},
      {"a class in a package reading the package's constant",
       "package p;\n  typedef enum {A, B} e_t;\n  enum {X, Y} v;\n  class C;\n"
       "    parameter e_t E = Y;\n  endclass\nendpackage\nmodule m;\n"
       "endmodule\n",
       "E", 5},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability, InPlaceEnumConstantIsReportedInEveryBlock) {
  const IncompatibleValue kCases[] = {
      {"a function variable",
       "typedef enum {A, B} e_t;\nmodule m;\n  function int f();\n"
       "    enum {X, Y} v;\n    parameter e_t E = Y;\n    return 0;\n"
       "  endfunction\nendmodule\n",
       "E", 5},
      {"a function argument",
       "typedef enum {A, B} e_t;\nmodule m;\n"
       "  function int f(enum {X, Y} a);\n    parameter e_t E = Y;\n"
       "    return 0;\n  endfunction\nendmodule\n",
       "E", 4},
      {"a task variable",
       "typedef enum {A, B} e_t;\nmodule m;\n  task t();\n"
       "    enum {X, Y} v;\n    parameter e_t E = Y;\n  endtask\nendmodule\n",
       "E", 5},
      {"a named block variable",
       "typedef enum {A, B} e_t;\nmodule m;\n  initial begin : b\n"
       "    enum {X, Y} v;\n    parameter e_t E = Y;\n  end\nendmodule\n",
       "E", 5},
      {"a named block parameter",
       "typedef enum {A, B} e_t;\nmodule m;\n  initial begin : b\n"
       "    parameter enum {X, Y} F = X;\n    parameter e_t E = Y;\n  end\n"
       "endmodule\n",
       "E", 5},
      {"a named block structure member",
       "typedef enum {A, B} e_t;\nmodule m;\n  initial begin : b\n"
       "    struct {enum {X, Y} f;} s;\n    parameter e_t E = Y;\n  end\n"
       "endmodule\n",
       "E", 5},
      {"a named block typedef",
       "typedef enum {A, B} e_t;\nmodule m;\n  initial begin : b\n"
       "    typedef enum {X, Y} f_t;\n    parameter e_t E = Y;\n  end\n"
       "endmodule\n",
       "E", 5},
      {"a named block constant named by a range",
       "typedef enum {A, B} e_t;\nmodule m;\n  initial begin : b\n"
       "    enum {X[2]} v;\n    parameter e_t E = X1;\n  end\nendmodule\n",
       "E", 5},
      {"an inner block reading its outer block's constant",
       "typedef enum {A, B} e_t;\nmodule m;\n  initial begin : b\n"
       "    enum {X, Y} v;\n    begin : c\n      parameter e_t E = Y;\n"
       "    end\n  end\nendmodule\n",
       "E", 6},
      {"a named block importing a package",
       "package p;\n  enum {X, Y} v;\nendpackage\ntypedef enum {A, B} e_t;\n"
       "module m;\n  initial begin : b\n    import p::*;\n"
       "    parameter e_t E = Y;\n  end\nendmodule\n",
       "E", 8},
      {"a package function",
       "package p;\n  typedef enum {A, B} e_t;\n"
       "  function automatic int f();\n    enum {X, Y} v;\n"
       "    parameter e_t E = Y;\n    return 0;\n  endfunction\nendpackage\n"
       "module m;\nendmodule\n",
       "E", 5},
      {"a class method",
       "typedef enum {A, B} e_t;\nclass C;\n  function int f();\n"
       "    enum {X, Y} v;\n    parameter e_t E = Y;\n    return 0;\n"
       "  endfunction\nendclass\nmodule m;\nendmodule\n",
       "E", 5},
      {"a class method reading its class's constant",
       "typedef enum {A, B} e_t;\nclass C;\n  enum {X, Y} v;\n"
       "  function int f();\n    parameter e_t E = Y;\n    return 0;\n"
       "  endfunction\nendclass\nmodule m;\nendmodule\n",
       "E", 5},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability, InPlaceEnumConstantIsReportedHoweverNamed) {
  const IncompatibleValue kCases[] = {
      {"a package constant by its scoped name",
       "package p;\n  enum {X, Y} v;\nendpackage\ntypedef enum {A, B} e_t;\n"
       "module m;\n  parameter e_t E = p::Y;\nendmodule\n",
       "E", 6},
      {"a package constant a wildcard import brings in",
       "package p;\n  enum {X, Y} v;\nendpackage\ntypedef enum {A, B} e_t;\n"
       "module m;\n  import p::*;\n  parameter e_t E = Y;\nendmodule\n",
       "E", 7},
      {"a package constant an explicit import brings in",
       "package p;\n  enum {X, Y} v;\nendpackage\ntypedef enum {A, B} e_t;\n"
       "module m;\n  import p::Y;\n  parameter e_t E = Y;\nendmodule\n",
       "E", 7},
      {"a package constant imported into another package",
       "package q;\n  enum {X, Y} v;\nendpackage\npackage p;\n  import q::*;\n"
       "  typedef enum {A, B} e_t;\n  parameter e_t E = Y;\nendpackage\n"
       "module m;\nendmodule\n",
       "E", 7},
      {"a compilation-unit constant by its scoped name",
       "typedef enum {A, B} e_t;\nenum {X, Y} v;\nmodule m;\n"
       "  parameter e_t E = $unit::Y;\nendmodule\n",
       "E", 4},
      {"a class constant by its scoped name",
       "typedef enum {A, B} e_t;\nclass C;\n  enum {X, Y} v;\nendclass\n"
       "module m;\n  parameter e_t E = C::Y;\nendmodule\n",
       "E", 6},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability, InPlaceEnumConstantIsReportedInEveryOverride) {
  const IncompatibleValue kCases[] = {
      {"an instance override",
       "typedef enum {A, B} e_t;\nmodule c #(parameter e_t E = A);\n"
       "endmodule\nmodule t;\n  enum {X, Y} v;\n  c #(.E(Y)) u();\n"
       "endmodule\n",
       "E", 6},
      {"an instance override in a generate block",
       "typedef enum {A, B} e_t;\nmodule c #(parameter e_t E = A);\n"
       "endmodule\nmodule t;\n  if (1) begin : g\n    enum {X, Y} v;\n"
       "    c #(.E(Y)) u();\n  end\nendmodule\n",
       "E", 7},
      {"a defparam",
       "typedef enum {A, B} e_t;\nmodule c;\n  parameter e_t E = A;\n"
       "endmodule\nmodule t;\n  enum {X, Y} v;\n  c u();\n"
       "  defparam u.E = Y;\nendmodule\n",
       "E", 8},
      {"a class specialization",
       "typedef enum {A, B} e_t;\nclass C #(e_t E = A);\nendclass\n"
       "module m;\n  enum {X, Y} v;\n  C #(.E(Y)) h;\nendmodule\n",
       "E", 6},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability, EnumConstantIsJudgedAsItsReadersScopeSeesIt) {
  const IncompatibleValue kCases[] = {
      {"a module constant hiding a compilation-unit one",
       "typedef enum {X, Y} e_t;\nmodule m;\n  enum {P, Y} w;\n"
       "  parameter e_t E = Y;\nendmodule\n",
       "E", 4},
      {"a module constant hiding a wildcard-imported one",
       "package p;\n  typedef enum {X, Y} e_t;\nendpackage\nmodule m;\n"
       "  import p::*;\n  enum {P, Y} w;\n  parameter e_t E = Y;\n"
       "endmodule\n",
       "E", 7},
      {"a constant another module also declares",
       "module m1;\n  typedef enum {X, Y} e_t;\n  typedef enum {P, Q} f_t;\n"
       "  parameter f_t F = Y;\nendmodule\nmodule m2;\n"
       "  typedef enum {Y, Z} g_t;\nendmodule\n",
       "F", 4},
      {"a class constant hiding a compilation-unit one",
       "typedef enum {X, Y} e_t;\nclass C;\n  enum {P, Y} w;\n"
       "  parameter e_t E = Y;\nendclass\nmodule m;\nendmodule\n",
       "E", 4},
      {"a block constant hiding a module one",
       "module m;\n  typedef enum {X, Y} e_t;\n  initial begin : b\n"
       "    enum {P, Y} w;\n    parameter e_t E = Y;\n  end\nendmodule\n",
       "E", 5},
      {"a generate block parameter hiding a module constant",
       "module m;\n  typedef enum {X, Y} f_t;\n  if (1) begin : g\n"
       "    parameter int Y = 1;\n    parameter f_t F = Y;\n  end\n"
       "endmodule\n",
       "F", 5},
  };
  ExpectEachReported(kCases);
}

TEST(ParamValueAssignability,
     InPlaceEnumConstantOfItsTypeOrForAnIntIsAccepted) {
  const char* const kSources[] = {
      "typedef enum {A, B} e_t;\n"
      "module m #(parameter enum {X, Y} F = Y, parameter int I = X);\n"
      "  enum {P, Q} v;\n  wire enum logic {R, S} w;\n"
      "  struct {enum {T, U} f;} s;\n  enum {V[2]} r;\n"
      "  parameter int J1 = Q;\n  parameter int J2 = S;\n"
      "  parameter int J3 = U;\n  parameter int J4 = V1;\n"
      "  parameter enum {G, H} K = H;\n  parameter e_t E = B;\n"
      "  if (1) begin : g\n    enum {L, M} z;\n    parameter int N = M;\n"
      "    parameter int O = Q;\n  end\nendmodule\n",
      "interface i;\n  enum {X, Y} v;\n  parameter int I = Y;\n"
      "  parameter enum {P, Q} F = Q;\nendinterface\nprogram pr;\n"
      "  enum {X, Y} v;\n  parameter int I = Y;\nendprogram\nmodule m;\n"
      "  i u();\n  pr w();\nendmodule\n",
      "package p;\n  typedef enum {A, B} e_t;\n  enum {X, Y} v;\n"
      "  struct {enum {P, Q} f;} s;\n  enum {R[2]} r;\n"
      "  parameter int I = Y;\n  parameter int J = Q;\n"
      "  parameter int K = R1;\n  parameter enum {G, H} F = H;\n"
      "  parameter e_t E = B;\nendpackage\nmodule m;\n"
      "  parameter int L = p::Y;\n  import p::*;\n  parameter int N = X;\n"
      "endmodule\n",
      "enum {X, Y} v;\nstruct {enum {P, Q} f;} s;\nparameter int I = Y;\n"
      "parameter int J = Q;\nparameter enum {G, H} F = H;\nmodule m;\n"
      "  parameter int K = $unit::Y;\nendmodule\n",
      "class C #(enum {X, Y} F = Y, int I = X);\n  enum {P, Q} v;\n"
      "  typedef enum {R, S} f_t;\n  parameter int J = Q;\n"
      "  parameter f_t K = S;\n  parameter enum {G, H} L = H;\n"
      "  function int f();\n    parameter int N = Q;\n    return 0;\n"
      "  endfunction\nendclass\nclass D;\n  enum {T, U} w;\nendclass\n"
      "module m;\n  parameter int M = D::U;\nendmodule\n",
      "module m;\n  function int f(enum {X, Y} a);\n    enum {P, Q} v;\n"
      "    typedef enum {R, S} f_t;\n    parameter int I = Y;\n"
      "    parameter int J = Q;\n    parameter f_t K = S;\n"
      "    parameter enum {G, H} L = H;\n    return 0;\n  endfunction\n"
      "  initial begin : b\n    struct {enum {T, U} f;} s;\n"
      "    parameter int M = U;\n    begin : c\n      parameter int N = U;\n"
      "    end\n  end\nendmodule\n",
      "package p;\n  typedef enum {X, Y} e_t;\nendpackage\nmodule m;\n"
      "  initial begin : b\n    import p::*;\n    parameter e_t E = Y;\n"
      "    parameter int I = X;\n  end\nendmodule\n",
      "module c #(parameter int I = 0);\n  parameter int J = 0;\nendmodule\n"
      "class C #(int I = 0);\nendclass\nmodule t;\n  enum {X, Y} v;\n"
      "  c #(.I(Y)) u();\n  c w();\n  defparam w.J = Y;\n  C #(.I(Y)) h;\n"
      "endmodule\n",
  };
  ExpectEachAccepted(kSources);
}

TEST(ParamValueAssignability, EnumConstantIsAcceptedAsItsReadersScopeSeesIt) {
  const char* const kSources[] = {
      "enum {X, Y} v;\nmodule m;\n  typedef enum {P, Y} f_t;\n"
      "  parameter f_t F = Y;\nendmodule\n",
      "module m1;\n  typedef enum {X, Y} e_t;\n  parameter e_t E = Y;\n"
      "endmodule\nmodule m2;\n  typedef enum {Y, Z} g_t;\n"
      "  parameter g_t G = Y;\nendmodule\n",
      "enum {X, Y} v;\nclass C;\n  typedef enum {P, Y} f_t;\n"
      "  parameter f_t F = Y;\nendclass\nmodule m;\nendmodule\n",
      "module m;\n  parameter int Y = 1;\n  if (1) begin : g\n"
      "    typedef enum {X, Y} f_t;\n    parameter f_t F = Y;\n  end\n"
      "endmodule\n",
      "typedef enum {A, B} e_t;\nmodule m;\n  if (1) begin : g1\n"
      "    if (1) begin : h\n      enum {X, Y} v;\n    end\n  end\n"
      "  if (1) begin : g2\n    parameter e_t Y = B;\n"
      "    parameter e_t E = Y;\n  end\nendmodule\n",
  };
  ExpectEachAccepted(kSources);
}

}  // namespace
