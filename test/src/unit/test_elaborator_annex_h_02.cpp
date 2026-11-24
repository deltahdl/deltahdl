#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

bool ElaboratesCleanly(const std::string& src) {
  ElabFixture f;
  Elaborate(src, f, "m");
  return f.diag.Diagnostics().empty();
}

bool Reports(const std::string& src, const std::string& message, uint32_t line,
             const std::string& subclause) {
  ElabFixture f;
  Elaborate(src, f, "m");
  return ReportedError(f.diag.Diagnostics(), message, line, subclause);
}

std::string ModuleExportingResult(const std::string& type) {
  return "module m;\n"
         "  function " +
         type +
         " sv_give(); endfunction\n"
         "  export \"DPI-C\" function sv_give;\n"
         "endmodule\n";
}

TEST(DpiOpenArrayImport, ATasksFormalMayBeOpen) {
  EXPECT_TRUE(
      ElaboratesCleanly("module m;\n"
                        "  import \"DPI-C\" task c_t(input int data[]);\n"
                        "endmodule\n"));
}

TEST(DpiOpenArrayImport, AnImportOutsideAModuleMayHaveAnOpenFormal) {
  const std::string kImport =
      "import \"DPI-C\" function void c_f(input int d[]);\n";
  EXPECT_TRUE(ElaboratesCleanly("package p;\n" + kImport +
                                "endpackage\nmodule m; endmodule\n"));
  EXPECT_TRUE(ElaboratesCleanly("interface i;\n" + kImport +
                                "endinterface\nmodule m; i u(); endmodule\n"));
  EXPECT_TRUE(ElaboratesCleanly("program g;\n" + kImport +
                                "endprogram\nmodule m; g u(); endmodule\n"));
  EXPECT_TRUE(ElaboratesCleanly(kImport + "module m; endmodule\n"));
}

TEST(DpiOpenArrayImport,
     PackedActualsOfAnyDimensionCountMatchAnOpenPackedPart) {
  EXPECT_TRUE(
      ElaboratesCleanly("module m;\n"
                        "  import \"DPI-C\" function void f(input bit [] a);\n"
                        "  bit [3:0][7:0] x;\n"
                        "  bit [7:0] y;\n"
                        "  initial begin f(x); f(y); end\n"
                        "endmodule\n"));
}

TEST(DpiOpenArrayImport, AnActualsUnpackedDimensionsMatchOneForOne) {
  EXPECT_TRUE(ElaboratesCleanly(
      "module m;\n"
      "  import \"DPI-C\" function void f1(input int a[]);\n"
      "  import \"DPI-C\" function void f2(input int a[][]);\n"
      "  int v[0:1][0:2];\n"
      "  int x[4];\n"
      "  initial begin f2(v); f1(x); end\n"
      "endmodule\n"));
}

TEST(DpiOpenArrayImport,
     DISABLED_AnActualOfAnotherUnpackedDimensionCountIsRejected) {
  const std::string kHead =
      "module m;\n"
      "  import \"DPI-C\" function void f1(input int a[]);\n"
      "  import \"DPI-C\" function void f2(input int a[][]);\n"
      "  int v[0:1][0:2];\n"
      "  int x[4];\n";
  EXPECT_TRUE(Reports(kHead + "  initial f1(v);\nendmodule\n",
                      "array argument 'v' has 2 unpacked dimension(s) but "
                      "formal 'a' has 1",
                      6, "7.7"));
  EXPECT_TRUE(Reports(kHead + "  initial f2(x);\nendmodule\n",
                      "array argument 'x' has 1 unpacked dimension(s) but "
                      "formal 'a' has 2",
                      6, "7.7"));
}

TEST(DpiExportRestriction, AnOpenFormalIsRejectedOutsideAModule) {
  const std::string kExport =
      "function void sv_take(input int data[]); endfunction\n"
      "export \"DPI-C\" function sv_take;\n";
  const std::string kMessage =
      "SystemVerilog function 'sv_take' has a dynamic array formal argument "
      "and therefore cannot be exported for DPI";
  EXPECT_TRUE(
      Reports("package p;\n" + kExport + "endpackage\nmodule m; endmodule\n",
              kMessage, 3, "35.5.6"));
  EXPECT_TRUE(Reports(
      "interface i;\n" + kExport + "endinterface\nmodule m; i u(); endmodule\n",
      kMessage, 3, "35.5.6"));
  EXPECT_TRUE(Reports(
      "program g;\n" + kExport + "endprogram\nmodule m; g u(); endmodule\n",
      kMessage, 3, "35.5.6"));
}

TEST(DpiExportRestriction, ASizedPackedFormalIsAccepted) {
  EXPECT_TRUE(
      ElaboratesCleanly("module m;\n"
                        "  function void sv_take(input bit [7:0] a);\n"
                        "  endfunction\n"
                        "  export \"DPI-C\" function sv_take;\n"
                        "endmodule\n"));
}

TEST(DpiExportRestriction, ARefFormalIsRejectedOutsideAModuleBody) {
  const std::string kExport =
      "function automatic void sv_f(ref int x); endfunction\n"
      "export \"DPI-C\" function sv_f;\n";
  const std::string kMessage =
      "SystemVerilog function 'sv_f' has a ref argument and therefore cannot "
      "be exported";
  EXPECT_TRUE(
      Reports("package p;\n" + kExport + "endpackage\nmodule m; endmodule\n",
              kMessage, 3, "35.7"));
  EXPECT_TRUE(Reports(
      "interface i;\n" + kExport + "endinterface\nmodule m; i u(); endmodule\n",
      kMessage, 3, "35.7"));
  EXPECT_TRUE(
      Reports("module m;\nif (1) begin : b\n" + kExport + "end\nendmodule\n",
              kMessage, 4, "35.7"));
}

TEST(DpiExportRestriction, AnInputFormalIsAcceptedOutsideAModuleBody) {
  const std::string kExport =
      "function automatic void sv_f(input int x); endfunction\n"
      "export \"DPI-C\" function sv_f;\n";
  EXPECT_TRUE(ElaboratesCleanly("package p;\n" + kExport +
                                "endpackage\nmodule m; endmodule\n"));
  EXPECT_TRUE(ElaboratesCleanly("interface i;\n" + kExport +
                                "endinterface\nmodule m; i u(); endmodule\n"));
  EXPECT_TRUE(ElaboratesCleanly("program g;\n" + kExport +
                                "endprogram\nmodule m; g u(); endmodule\n"));
  EXPECT_TRUE(ElaboratesCleanly("module m;\nif (1) begin : b\n" + kExport +
                                "end\nendmodule\n"));
}

TEST(DpiExportRestriction, ATasksQueueFormalIsRejected) {
  EXPECT_TRUE(Reports(
      "module m;\n"
      "  task sv_t(input int q[$]); endtask\n"
      "  export \"DPI-C\" task sv_t;\n"
      "endmodule\n",
      "SystemVerilog task 'sv_t' has a formal argument 'q' with a queue "
      "dimension, which is not a permitted formal argument type for DPI",
      3, "35.5.6"));
}

TEST(DpiExportRestriction, ATasksUnpackedUnionFormalIsRejected) {
  const std::string kFormal =
      " {int a; bit [31:0] b;} u_t;\n"
      "module m;\n"
      "  task sv_t(input u_t u); endtask\n"
      "  export \"DPI-C\" task sv_t;\n"
      "endmodule\n";
  EXPECT_TRUE(Reports("typedef union" + kFormal,
                      "SystemVerilog task 'sv_t' has an unpacked union formal "
                      "argument 'u'; only the packed form of a union is "
                      "permitted for DPI",
                      4, "35.5.6"));
  EXPECT_TRUE(ElaboratesCleanly("typedef union packed" + kFormal));
}

TEST(DpiExportRestriction, EveryPermittedResultTypeIsAccepted) {
  for (const char* type :
       {"byte", "shortint", "int", "longint", "real", "shortreal", "chandle",
        "string", "bit", "logic", "void"}) {
    EXPECT_TRUE(ElaboratesCleanly(ModuleExportingResult(type))) << type;
  }
}

TEST(DpiExportRestriction, AResultTypeOutsideThePermittedOnesIsRejected) {
  for (const char* type : {"time", "e_t", "s_t"}) {
    EXPECT_TRUE(
        Reports("typedef enum {A, B} e_t;"
                "typedef struct packed {bit a; bit b;} s_t;" +
                    ModuleExportingResult(type),
                "exported function 'sv_give' has a result type that "
                "is not permitted for DPI",
                3, "35.5.5"))
        << type;
  }
}

TEST(DpiExportRestriction, DISABLED_AClassResultIsRejected) {
  EXPECT_TRUE(Reports("class C; endclass\n" + ModuleExportingResult("C"),
                      "exported function 'sv_give' has a class type as its "
                      "result, which cannot be passed through the DPI",
                      4, "35.5.5"));
}

}  // namespace
