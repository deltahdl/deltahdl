#include <gtest/gtest.h>

#include <cstdarg>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>

#include "helpers_run_files.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct OpenResults {
  PLI_UINT32 first = 0;
  PLI_UINT32 second = 0;
  PLI_UINT32 third = 1;
  std::string seen;
};

OpenResults results;

std::string TextNow(const std::string& name) {
  std::ifstream file(name);
  std::stringstream text;
  text << file.rdbuf();
  return text.str();
}

PLI_INT32 PrintThroughAList(PLI_UINT32 mcd, const char* format, ...) {
  va_list args{};
  va_start(args, format);
  const PLI_INT32 kCount = vpi_mcd_vprintf(mcd, VpiText(format), args);
  va_end(args);
  return kCount;
}

void PutDescriptor(const char* name, PLI_UINT32 mcd) {
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = static_cast<PLI_INT32>(mcd);
  vpi_put_value(vpi_handle_by_name(VpiText(name), nullptr), &value, nullptr,
                vpiNoDelay);
}

class McdOpenInARun : public RunFilesRun {
 protected:
  void SetUp() override {
    RunFilesRun::SetUp();
    results = {};
  }

  void RunTask(PLI_INT32 (*calltf)(PLI_BYTE8*)) {
    RegisterTask("$open", calltf);
    Run("module top; initial $open; endmodule\n");
  }

  static PLI_INT32 ReopenAfterAWrite(PLI_BYTE8*) {
    results.first = vpi_mcd_open(VpiText("r.txt"));
    vpi_mcd_printf(results.first, VpiText("first\n"));
    vpi_mcd_flush(results.first);
    results.second = vpi_mcd_open(VpiText("r.txt"));
    vpi_mcd_printf(results.second, VpiText("second\n"));
    vpi_mcd_close(results.first);
    return 0;
  }

  static PLI_INT32 OpenUnderOtherSpellings(PLI_BYTE8*) {
    results.first = vpi_mcd_open(VpiText("s.txt"));
    results.second = vpi_mcd_open(VpiText("./s.txt"));
    const std::string kAbsolute =
        (std::filesystem::current_path() / "s.txt").string();
    results.third = vpi_mcd_open(VpiText(kAbsolute.c_str()));
    return 0;
  }

  static PLI_INT32 OpenWhatTheFileSystemRefuses(PLI_BYTE8*) {
    results.first = vpi_mcd_open(VpiText("no_such_dir/x.txt"));
    results.second = vpi_mcd_open(VpiText("a_directory"));
    results.third = vpi_mcd_open(VpiText("writable.txt"));
    return 0;
  }

  static PLI_INT32 OpenAnExistingFile(PLI_BYTE8*) {
    results.first = vpi_mcd_open(VpiText("e.txt"));
    vpi_mcd_printf(results.first, VpiText("new\n"));
    vpi_mcd_close(results.first);
    return 0;
  }

  static PLI_INT32 OpenForTheDesign(PLI_BYTE8*) {
    results.first = vpi_mcd_open(VpiText("v.txt"));
    PutDescriptor("top.v", results.first);
    return 0;
  }

  static PLI_INT32 ReadAfterTheFlush(PLI_BYTE8*) {
    results.seen = TextNow("v.txt");
    return 0;
  }

  static PLI_INT32 PrintThroughTheDesignsMcd(PLI_BYTE8*) {
    results.first = DescriptorIn("top.mcd");
    PrintThroughAList(results.first, "via vprintf %d\n", 7);
    return 0;
  }
};

TEST_F(McdOpenInARun, AReopenAfterAWriteKeepsTheText) {
  RunTask(&ReopenAfterAWrite);
  ASSERT_NE(results.first, 0u);
  EXPECT_EQ(results.second, results.first);
  EXPECT_EQ(FileText("r.txt"), "first\nsecond\n");
}

TEST_F(McdOpenInARun, DISABLED_AnotherSpellingOfAnOpenFileGivesItsMcd) {
  RunTask(&OpenUnderOtherSpellings);
  ASSERT_NE(results.first, 0u);
  EXPECT_EQ(results.second, results.first);
  EXPECT_EQ(results.third, results.first);
}

TEST_F(McdOpenInARun, AnOpenTheFileSystemRefusesReturnsZero) {
  std::filesystem::create_directory("a_directory");
  std::ofstream("writable.txt") << "";
  RunTask(&OpenWhatTheFileSystemRefuses);
  EXPECT_EQ(results.first, 0u);
  EXPECT_EQ(results.second, 0u);
  EXPECT_NE(results.third, 0u);
  EXPECT_TRUE(std::filesystem::is_directory("a_directory"));
}

TEST_F(McdOpenInARun, AnExistingFilesContentsAreReplaced) {
  std::ofstream("e.txt") << "old contents\n";
  RunTask(&OpenAnExistingFile);
  ASSERT_NE(results.first, 0u);
  EXPECT_EQ(FileText("e.txt"), "new\n");
}

TEST_F(McdOpenInARun, TheDesignsFileTasksActOnAVpiMcd) {
  RegisterTask("$open", &OpenForTheDesign);
  RegisterTask("$read_back", &ReadAfterTheFlush);
  Run("module top; integer v; integer x = 0;\n"
      "  initial begin\n"
      "    $open;\n"
      "    $fwrite(v, \"w;\");\n"
      "    $fflush(v);\n"
      "    $read_back;\n"
      "    $fmonitor(v, \"m%0d;\", x);\n"
      "    $fstrobe(v, \"s;\");\n"
      "    #1 x = 1;\n"
      "    #1 $fclose(v);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(results.first, 0u);
  EXPECT_EQ(results.seen, "w;");
  const std::string kText = FileText("v.txt");
  EXPECT_EQ(kText.rfind("w;", 0), 0u);
  EXPECT_NE(kText.find("s;"), std::string::npos);
  EXPECT_NE(kText.find("m0;"), std::string::npos);
  EXPECT_NE(kText.find("m1;"), std::string::npos);
}

TEST_F(McdOpenInARun, VprintfWritesThroughTheDesignsMcd) {
  RegisterTask("$print", &PrintThroughTheDesignsMcd);
  Run("module top; integer mcd;\n"
      "  initial begin\n"
      "    mcd = $fopen(\"d.txt\");\n"
      "    $print;\n"
      "    $fclose(mcd);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(results.first, 0u);
  EXPECT_EQ(FileText("d.txt"), "via vprintf 7\n");
}

}  // namespace
}  // namespace delta
