#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "helpers_c_compiler.h"

namespace {

const char* MacroProbes() {
  return R"(import_spec[DPI_DLLISPEC]
export_spec[DPI_DLLESPEC]
#if defined(DPI_EXTERN) || defined(DPI_PROTOTYPES)
switches_survive
#endif
#if defined(XXTERN) || defined(EETERN)
markers_survive
#endif
)";
}

std::string PreprocessedHeader(const std::string& prologue,
                               const std::vector<std::string>& flags) {
  std::string source = prologue;
  source += "#include \"simulator/svdpi.h\"\n";
  source += MacroProbes();
  return PreprocessedWithoutSpaces(source, flags);
}

bool Holds(const std::string& text, const std::string& part) {
  return text.find(part) != std::string::npos;
}

size_t CountOf(const std::string& text, const std::string& part) {
  size_t count = 0;
  for (size_t at = text.find(part); at != std::string::npos;
       at = text.find(part, at + part.size())) {
    ++count;
  }
  return count;
}

TEST(SvdpiLinkageSpecs, BothSpecsAreEmptyOffWindows) {
  std::string text = PreprocessedHeader("", {"-x", "c"});
  EXPECT_TRUE(Holds(text, "import_spec[]")) << text;
  EXPECT_TRUE(Holds(text, "export_spec[]")) << text;
  EXPECT_FALSE(Holds(text, "__declspec"));
}

TEST(SvdpiLinkageSpecs, EachWindowsToolchainMacroSelectsTheDllSpecs) {
  for (const char* macro : {"_MSC_VER", "__MINGW32__", "__CYGWIN__"}) {
    std::string prologue = "#define ";
    prologue += macro;
    prologue += " 1\n";
    std::string text = PreprocessedHeader(prologue, {"-x", "c"});
    EXPECT_TRUE(Holds(text, "import_spec[__declspec(dllimport)]")) << macro;
    EXPECT_TRUE(Holds(text, "export_spec[__declspec(dllexport)]")) << macro;
    EXPECT_TRUE(
        Holds(text, "__declspec(dllimport)constchar*svDpiVersion(void);"))
        << macro;
  }
}

TEST(SvdpiLinkageMacros, NothingIsAddedToADeclarationByDefault) {
  std::string text = PreprocessedHeader("", {"-x", "c", "-dD"});
  EXPECT_TRUE(Holds(text, "constchar*svDpiVersion(void);"));
  EXPECT_FALSE(Holds(text, "externconstchar*svDpiVersion"));
  EXPECT_TRUE(Holds(text, "#defineXXTERNDPI_EXTERNDPI_DLLISPEC")) << text;
  EXPECT_TRUE(Holds(text, "#defineEETERNDPI_EXTERNDPI_DLLESPEC")) << text;
  EXPECT_FALSE(Holds(text, "switches_survive"));
  EXPECT_FALSE(Holds(text, "markers_survive"));
}

TEST(SvdpiLinkageMacros, AnIncludersExternMarkIsKeptUntilTheEnd) {
  std::string text = PreprocessedHeader(
      "#define DPI_EXTERN extern INCLUDERS_MARK\n", {"-x", "c", "-dD"});
  EXPECT_TRUE(Holds(text, "externINCLUDERS_MARKconstchar*svDpiVersion(void);"))
      << text;
  EXPECT_EQ(CountOf(text, "#defineDPI_EXTERN"), 1u);
  EXPECT_TRUE(Holds(text, "#defineXXTERNDPI_EXTERNDPI_DLLISPEC"));
  EXPECT_TRUE(Holds(text, "#defineEETERNDPI_EXTERNDPI_DLLESPEC"));
  EXPECT_FALSE(Holds(text, "switches_survive"));
  EXPECT_FALSE(Holds(text, "markers_survive"));
}

TEST(SvdpiLinkageMacros, AnIncludersPrototypeMarkersAreKeptUntilTheEnd) {
  std::string text = PreprocessedHeader(
      "#define DPI_PROTOTYPES\n"
      "#define XXTERN INCLUDERS_IMPORT\n"
      "#define EETERN INCLUDERS_EXPORT\n",
      {"-x", "c", "-dD"});
  EXPECT_TRUE(Holds(text, "INCLUDERS_IMPORTconstchar*svDpiVersion(void);"))
      << text;
  EXPECT_EQ(CountOf(text, "#defineDPI_PROTOTYPES"), 1u);
  EXPECT_EQ(CountOf(text, "#defineXXTERN"), 1u);
  EXPECT_EQ(CountOf(text, "#defineEETERN"), 1u);
  EXPECT_FALSE(Holds(text, "switches_survive"));
  EXPECT_FALSE(Holds(text, "markers_survive"));
}

TEST(SvdpiLanguageLinkage, ACxxInclusionIsBracketedInCLinkage) {
  std::string text = PreprocessedHeader("", {"-x", "c++"});
  EXPECT_EQ(CountOf(text, "extern\"C\"{"), 1u);
}

TEST(SvdpiLanguageLinkage, ACInclusionCarriesNoLinkageSpecification) {
  std::string text = PreprocessedHeader("", {"-x", "c"});
  EXPECT_FALSE(Holds(text, "extern\"C\"")) << text;
  CompilerResult run = CompileAsC(R"(#include "simulator/svdpi.h"
const char* version(void);
const char* version(void) { return svDpiVersion(); }
)");
  EXPECT_TRUE(run.succeeded) << run.output;
}

TEST(SvdpiInclusionGuard, ASecondInclusionAddsNothing) {
  CompilerResult run = CompileAsC(R"(#include "simulator/svdpi.h"
#include "simulator/svdpi.h"
svLogicVecVal chunk;
)");
  EXPECT_TRUE(run.succeeded) << run.output;
  std::string text = PreprocessedWithoutSpaces(
      "#define INCLUDED_SVDPI\n#include \"simulator/svdpi.h\"\n", {"-x", "c"});
  EXPECT_EQ(text, "");
}

TEST(SvdpiStructTags, TheHeadersStructsCarryTheListingsTags) {
  CompilerResult run = CompileAsCxx(R"(#include "simulator/svdpi.h"
#include <type_traits>
static_assert(std::is_same<struct t_vpi_vecval, s_vpi_vecval>::value, "");
static_assert(std::is_same<struct t_vpi_vecval, svLogicVecVal>::value, "");
static_assert(std::is_same<struct t_vpi_vecval*, p_vpi_vecval>::value, "");
static_assert(std::is_same<struct t_vpi_time, s_vpi_time>::value, "");
static_assert(std::is_same<struct t_vpi_time, svTimeVal>::value, "");
static_assert(std::is_same<struct t_vpi_time*, p_vpi_time>::value, "");
)");
  EXPECT_TRUE(run.succeeded) << run.output;
}

TEST(SvdpiTimeGuard, AnIncludersTimeStructIsKept) {
  CompilerResult run = CompileAsCxx(R"(#define VPI_TIME
typedef struct includers_time {
  long whole_time;
} s_vpi_time, *p_vpi_time;
#include "simulator/svdpi.h"
#include <type_traits>
static_assert(std::is_same<svTimeVal, includers_time>::value, "");
static_assert(sizeof(svTimeVal::whole_time) == sizeof(long), "");
#if defined(vpiScaledRealTime) || defined(vpiSimTime) || \
    defined(vpiSuppressTime)
#error the time value codes were defined
#endif
)");
  EXPECT_TRUE(run.succeeded) << run.output;
}

TEST(SvdpiTimeGuard, TheVpiHeadersTimeStructIsKeptWhenItComesFirst) {
  CompilerResult run = CompileAsCxx(R"(#include <stdint.h>
#include "simulator/vpi_user.h"
typedef s_vpi_time vpi_time;
typedef s_vpi_vecval vpi_vecval;
#include "simulator/svdpi.h"
#include <type_traits>
static_assert(std::is_same<svTimeVal, vpi_time>::value, "");
static_assert(std::is_same<svLogicVecVal, vpi_vecval>::value, "");
static_assert(sv_scaled_real_time == 1 && sv_sim_time == 2, "");
)");
  EXPECT_TRUE(run.succeeded) << run.output;
}

}  // namespace
