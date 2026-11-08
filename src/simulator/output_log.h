#pragma once

#include <fstream>
#include <ios>
#include <ostream>
#include <streambuf>
#include <string>
#include <string_view>

namespace delta {

class OutputLog {
 public:
  OutputLog();

  std::ostream& Out() { return out_; }

  void Open(std::string_view name);

  void Enable() { enabled_ = true; }
  void Disable() { enabled_ = false; }
  bool Enabled() const { return enabled_; }

  const std::string& Name() const { return name_; }

  void Copy(std::string_view text);

 private:
  class TeeBuf : public std::streambuf {
   public:
    explicit TeeBuf(OutputLog& log) : log_(log) {}

   protected:
    int_type overflow(int_type ch) override;
    std::streamsize xsputn(const char* s, std::streamsize n) override;
    int sync() override;

   private:
    OutputLog& log_;
  };

  TeeBuf buf_;
  std::ostream out_;
  std::ofstream file_;
  std::string name_;
  bool enabled_ = true;
};

}  // namespace delta
