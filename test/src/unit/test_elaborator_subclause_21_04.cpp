#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string LoadIn(const std::string& call) {
  return "module t;\n"
         "  reg [7:0] mem [0:3];\n"
         "  reg [7:0] r;\n"
         "  real fr;\n"
         "  string fs;\n"
         "  initial " +
         call +
         ";\n"
         "endmodule\n";
}

void ExpectReported(const std::string& call, const std::string& message) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(LoadIn(call), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 6, "21.4")) << call;
}

void ExpectAccepted(const std::string& call) {
  ElabFixture f;
  Elaborate(LoadIn(call), f);
  EXPECT_FALSE(f.has_errors) << call;
}

std::string Shape(const std::string& task) {
  return task +
         " takes a filename, a memory and an optional start address and "
         "finish address";
}

TEST(ReadmemArgumentList, DISABLED_NoArgumentIsReported) {
  for (const char* task : {"$readmemh", "$readmemb"}) {
    ExpectReported(std::string(task) + "()", Shape(task));
  }
}

TEST(ReadmemArgumentList, DISABLED_AFilenameAloneIsReported) {
  for (const char* task : {"$readmemh", "$readmemb"}) {
    ExpectReported(std::string(task) + "(\"f\")", Shape(task));
  }
}

TEST(ReadmemArgumentList, DISABLED_FiveArgumentsAreReported) {
  for (const char* task : {"$readmemh", "$readmemb"}) {
    ExpectReported(std::string(task) + "(\"f\", mem, 0, 3, 1)", Shape(task));
  }
}

TEST(ReadmemArgumentList, DISABLED_AFinishWithAnEmptyStartIsReported) {
  for (const char* task : {"$readmemh", "$readmemb"}) {
    ExpectReported(std::string(task) + "(\"f\", mem, , 1)", Shape(task));
  }
}

TEST(ReadmemArgumentList, DISABLED_AnEmptyFilenameOrMemoryIsReported) {
  for (const char* task : {"$readmemh", "$readmemb"}) {
    ExpectReported(std::string(task) + "(, mem)", Shape(task));
    ExpectReported(std::string(task) + "(\"f\", , 0)", Shape(task));
  }
}

TEST(ReadmemArgumentList, TwoThreeAndFourArgumentsAreAccepted) {
  for (const char* task : {"$readmemh", "$readmemb"}) {
    for (const char* tail :
         {"(\"f\", mem)", "(\"f\", mem, 1)", "(\"f\", mem, 0, 3)"}) {
      ExpectAccepted(std::string(task) + tail);
    }
  }
}

TEST(ReadmemFilename, DISABLED_ARealFilenameIsReported) {
  for (const char* task : {"$readmemh", "$readmemb"}) {
    ExpectReported(std::string(task) + "(fr, mem)",
                   std::string("the filename of ") + task +
                       " must be a string or an integral value");
  }
}

TEST(ReadmemFilename, StringAndIntegralFilenamesAreAccepted) {
  ExpectAccepted("$readmemh(fs, mem)");
  ExpectAccepted("$readmemb(\"f.mem\", mem)");
  ExpectAccepted("$readmemh(r, mem)");
}

TEST(ReadmemMemoryName, DISABLED_APlainVariableIsReported) {
  for (const char* task : {"$readmemh", "$readmemb"}) {
    ExpectReported(
        std::string(task) + "(\"f\", r)",
        std::string("the memory of ") + task + " must be an unpacked array");
  }
}

}  // namespace
