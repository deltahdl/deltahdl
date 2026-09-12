#include "simulator/output_log.h"

#include <cstddef>
#include <ios>
#include <iostream>
#include <string>
#include <string_view>

namespace delta {

OutputLog::OutputLog() : buf_(*this), out_(&buf_) {}

void OutputLog::Open(std::string_view name) {
  file_.close();
  file_.open(std::string(name), std::ios::binary);
  name_ = std::string(name);
  enabled_ = true;
}

void OutputLog::Copy(std::string_view text) {
  if (!enabled_ || !file_.is_open()) return;
  file_.write(text.data(), static_cast<std::streamsize>(text.size()));
  file_.flush();
}

OutputLog::TeeBuf::int_type OutputLog::TeeBuf::overflow(int_type ch) {
  char c = traits_type::to_char_type(ch);
  std::cout.put(c);
  log_.Copy(std::string_view(&c, 1));
  return traits_type::not_eof(ch);
}

std::streamsize OutputLog::TeeBuf::xsputn(const char* s, std::streamsize n) {
  std::cout.write(s, n);
  log_.Copy(std::string_view(s, static_cast<std::size_t>(n)));
  return n;
}

int OutputLog::TeeBuf::sync() {
  std::cout.flush();
  return 0;
}

}  // namespace delta
