#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "helpers_c_compiler.h"

namespace {

std::string Preprocessed(const std::string& prologue) {
  std::string source = prologue;
  source += R"(#include "simulator/vpi_user.h"
#ifdef PLI_DLLISPEC
import_spec[PLI_DLLISPEC]
#endif
#ifdef PLI_DLLESPEC
export_spec[PLI_DLLESPEC]
#endif
#if defined(VPI_USER_DEFINED_DLLISPEC) || defined(VPI_USER_DEFINED_DLLESPEC)
dll_markers_survive
#endif
#if defined(PLI_EXTERN) || defined(PLI_VEXTERN) || defined(PLI_PROTOTYPES)
switches_survive
#endif
#if defined(PROTO_PARAMS) || defined(XXTERN) || defined(EETERN)
prototype_macros_survive
#endif
)";
  return PreprocessedWithoutSpaces(source, {"-x", "c"});
}

bool Holds(const std::string& text, const std::string& part) {
  return text.find(part) != std::string::npos;
}

std::string Defining(const std::string& macro) {
  return "#define " + macro + " 1\n";
}

TEST(VpiLinkageSpecs, BothSpecsAreEmptyAndStayDefinedOffWindows) {
  std::string text = Preprocessed("");
  EXPECT_TRUE(Holds(text, "import_spec[]")) << text;
  EXPECT_TRUE(Holds(text, "export_spec[]"));
  EXPECT_FALSE(Holds(text, "__declspec"));
  EXPECT_FALSE(Holds(text, "dll_markers_survive"));
  EXPECT_TRUE(Holds(text, ";vpiHandlevpi_register_cb("));
}

TEST(VpiLinkageSpecs, AnIncludersSpecsAreUsedAndKept) {
  std::string mine =
      "#define PLI_DLLISPEC MY_IMPORT\n#define PLI_DLLESPEC MY_EXPORT\n";
  for (const std::string& prologue :
       {mine, Defining("_MSC_VER") + mine, Defining("__MINGW32__") + mine,
        Defining("__CYGWIN__") + mine}) {
    std::string text = Preprocessed(prologue);
    EXPECT_TRUE(Holds(text, "import_spec[MY_IMPORT]")) << prologue;
    EXPECT_TRUE(Holds(text, "export_spec[MY_EXPORT]")) << prologue;
    EXPECT_TRUE(Holds(text, ";MY_IMPORTvpiHandlevpi_register_cb("));
    EXPECT_TRUE(
        Holds(text, "externMY_EXPORTvoid(*vlog_startup_routines[])(void);"));
    EXPECT_FALSE(Holds(text, "dll_markers_survive"));
  }
}

TEST(VpiLinkageSpecs, EachWindowsToolchainGetsTheDllSpecsForTheFileAlone) {
  for (const char* macro : {"_MSC_VER", "__MINGW32__", "__CYGWIN__"}) {
    std::string text = Preprocessed(Defining(macro));
    EXPECT_TRUE(Holds(text, "__declspec(dllimport)vpiHandlevpi_register_cb("))
        << macro;
    EXPECT_TRUE(Holds(text,
                      "extern__declspec(dllexport)void"
                      "(*vlog_startup_routines[])(void);"))
        << macro;
    EXPECT_FALSE(Holds(text, "import_spec")) << macro;
    EXPECT_FALSE(Holds(text, "export_spec")) << macro;
    EXPECT_FALSE(Holds(text, "dll_markers_survive")) << macro;
  }
}

TEST(VpiLinkageMacros, AnIncludersExternMarksReachTheDeclarations) {
  std::string text = Preprocessed(
      "#define PLI_EXTERN extern MY_ROUTINE\n"
      "#define PLI_VEXTERN extern MY_VARIABLE\n");
  EXPECT_TRUE(Holds(text, ";externMY_ROUTINEvpiHandlevpi_register_cb("))
      << text;
  EXPECT_TRUE(
      Holds(text, "externMY_VARIABLEvoid(*vlog_startup_routines[])(void);"));
  EXPECT_FALSE(Holds(text, "switches_survive"));
  EXPECT_FALSE(Holds(text, "prototype_macros_survive"));
}

TEST(VpiLinkageMacros, AnIncludersPrototypeMacrosReachTheDeclarations) {
  std::string text = Preprocessed(
      "#define PLI_PROTOTYPES\n"
      "#define PROTO_PARAMS(params) MY_PARAMS params\n"
      "#define XXTERN MY_IMPORT\n"
      "#define EETERN MY_EXPORT\n");
  EXPECT_TRUE(Holds(text, ";MY_IMPORTvpiHandlevpi_register_cbMY_PARAMS("))
      << text;
  EXPECT_FALSE(Holds(text, "switches_survive"));
  EXPECT_FALSE(Holds(text, "prototype_macros_survive"));
}

TEST(VpiLinkageMacros, TheStartupArrayIsOnlyDeclared) {
  EXPECT_TRUE(
      Holds(Preprocessed(""), "externvoid(*vlog_startup_routines[])(void);"));
  CompilerResult run = CompileAsCxx(R"(#include <stdint.h>
#include "simulator/vpi_user.h"
static void startup() {}
void (*vlog_startup_routines[])(void) = {startup, 0};
)");
  EXPECT_TRUE(run.succeeded) << run.output;
}

TEST(VpiValueUnions, TheArmsAreTheListingsInItsOrder) {
  std::string text = Preprocessed("");
  EXPECT_TRUE(Holds(text,
                    "structt_vpi_value{PLI_INT32format;union{PLI_BYTE8*str;"
                    "PLI_INT32scalar;PLI_INT32integer;doublereal;"
                    "structt_vpi_time*time;structt_vpi_vecval*vector;"
                    "structt_vpi_strengthval*strength;PLI_BYTE8*misc;}value;}"
                    "s_vpi_value,*p_vpi_value;"))
      << text;
  EXPECT_TRUE(Holds(text,
                    "structt_vpi_arrayvalue{PLI_UINT32format;PLI_UINT32flags;"
                    "union{PLI_INT32*integers;PLI_INT16*shortints;"
                    "PLI_INT64*longints;PLI_BYTE8*rawvals;"
                    "structt_vpi_vecval*vectors;structt_vpi_time*times;"
                    "double*reals;float*shortreals;}value;}"
                    "s_vpi_arrayvalue,*p_vpi_arrayvalue;"));
}

const char* WidthChecks() {
  return R"(static_assert(sizeof(PLI_INT64) == 8 && sizeof(PLI_UINT64) == 8, "");
static_assert(sizeof(PLI_INT32) == 4 && sizeof(PLI_UINT32) == 4, "");
static_assert(sizeof(PLI_INT16) == 2 && sizeof(PLI_UINT16) == 2, "");
static_assert(sizeof(PLI_BYTE8) == 1 && sizeof(PLI_UBYTE8) == 1, "");
)";
}

TEST(VpiSizedTypeSources, TheMicrosoftBranchDeclaresTheTypesItself) {
  std::string text = Preprocessed(Defining("_MSC_VER"));
  EXPECT_TRUE(Holds(text,
                    "typedefunsigned__int64uint64_t;"
                    "typedefunsigned__int32uint32_t;"
                    "typedefunsigned__int8uint8_t;"
                    "typedefsigned__int64int64_t;"
                    "typedefsigned__int32int32_t;"
                    "typedefsigned__int8int8_t;"
                    "typedefint64_tPLI_INT64;typedefuint64_tPLI_UINT64;"))
      << text;
}

TEST(VpiSizedTypeSources, TheMicrosoftBranchsTypesHaveTheirStatedWidths) {
  std::string source = R"(#define _MSC_VER 1
#define __int64 long long
#define __int32 int
#define __int8 char
#define PLI_DLLISPEC
#define PLI_DLLESPEC
#include "simulator/vpi_user.h"
)";
  source += WidthChecks();
  CompilerResult run = CompileAsCxx(source);
  EXPECT_TRUE(run.succeeded) << run.output;
}

TEST(VpiSizedTypeSources, TheMingwBranchTakesTheTypesFromStdint) {
  std::string source = R"(#define __MINGW32__ 1
#define PLI_DLLISPEC
#define PLI_DLLESPEC
#include "simulator/vpi_user.h"
#ifndef INT64_MAX
#error stdint.h was not read
#endif
)";
  source += WidthChecks();
  CompilerResult run = CompileAsCxx(source);
  EXPECT_TRUE(run.succeeded) << run.output;
}

TEST(VpiSizedTypeSources, AnIncludersWideTypesAreKept) {
  CompilerResult run = CompileAsCxx(R"(#include <stdint.h>
#include <type_traits>
#define SVPI_TYPES
typedef struct wide_signed { double d; } PLI_INT64;
typedef float PLI_UINT64;
#include "simulator/vpi_user.h"
static_assert(std::is_same<PLI_INT64, wide_signed>::value, "");
static_assert(std::is_same<PLI_UINT64, float>::value, "");
static_assert(std::is_same<PLI_INT32, int>::value, "");
static_assert(std::is_same<PLI_UINT32, unsigned int>::value, "");
static_assert(std::is_same<PLI_INT16, short>::value, "");
static_assert(std::is_same<PLI_UINT16, unsigned short>::value, "");
static_assert(std::is_same<PLI_BYTE8, char>::value, "");
static_assert(std::is_same<PLI_UBYTE8, unsigned char>::value, "");
)");
  EXPECT_TRUE(run.succeeded) << run.output;
}

TEST(VpiSizedTypeSources, AnIncludersNarrowTypesAreKept) {
  CompilerResult run = CompileAsCxx(R"(#include <stdint.h>
#include <type_traits>
#define PLI_TYPES
typedef long PLI_INT32;
typedef unsigned long PLI_UINT32;
typedef int PLI_INT16;
typedef unsigned int PLI_UINT16;
typedef signed char PLI_BYTE8;
typedef bool PLI_UBYTE8;
#include "simulator/vpi_user.h"
static_assert(std::is_same<PLI_INT32, long>::value, "");
static_assert(std::is_same<vpiHandle, unsigned long*>::value, "");
static_assert(std::is_same<PLI_INT16, int>::value, "");
static_assert(std::is_same<PLI_UINT16, unsigned int>::value, "");
static_assert(std::is_same<PLI_BYTE8, signed char>::value, "");
static_assert(std::is_same<PLI_UBYTE8, bool>::value, "");
static_assert(std::is_same<PLI_INT64, int64_t>::value, "");
static_assert(std::is_same<PLI_UINT64, uint64_t>::value, "");
)");
  EXPECT_TRUE(run.succeeded) << run.output;
}

TEST(VpiStructureGuards, StructuresReadFirstFromTheDpiHeaderAreKept) {
  CompilerResult run = CompileAsCxx(R"(#include <stdint.h>
#include "simulator/svdpi.h"
typedef s_vpi_time dpi_time;
typedef s_vpi_vecval dpi_vecval;
#include "simulator/vpi_user.h"
#include <type_traits>
static_assert(std::is_same<s_vpi_time, dpi_time>::value, "");
static_assert(std::is_same<svTimeVal, s_vpi_time>::value, "");
static_assert(std::is_same<s_vpi_vecval, dpi_vecval>::value, "");
static_assert(std::is_same<svLogicVecVal, s_vpi_vecval>::value, "");
static_assert(sizeof(s_vpi_value) > 0 && sizeof(s_vpi_delay) > 0, "");
)");
  EXPECT_TRUE(run.succeeded) << run.output;
}

TEST(VpiStructureGuards, AnIncludersStructuresAndTimeTypesAreKept) {
  CompilerResult run = CompileAsCxx(R"(#include <stdint.h>
#define VPI_TIME
#define VPI_VECVAL
typedef struct t_vpi_time { long whole_time; } s_vpi_time, *p_vpi_time;
typedef struct t_vpi_vecval { long both; } s_vpi_vecval, *p_vpi_vecval;
#include "simulator/vpi_user.h"
static_assert(sizeof(s_vpi_time::whole_time) == sizeof(long), "");
static_assert(sizeof(s_vpi_vecval::both) == sizeof(long), "");
#if defined(vpiScaledRealTime) || defined(vpiSimTime) || \
    defined(vpiSuppressTime)
#error the time types were defined
#endif
)");
  EXPECT_TRUE(run.succeeded) << run.output;
}

TEST(VpiLanguageLinkage, OnlyACxxInclusionIsBracketedInCLinkage) {
  EXPECT_FALSE(Holds(Preprocessed(""), "extern\"C\""));
  std::string text = PreprocessedWithoutSpaces(
      "#include \"simulator/vpi_user.h\"\n", {"-x", "c++"});
  EXPECT_TRUE(Holds(text, "extern\"C\"{")) << text;
}

}  // namespace
