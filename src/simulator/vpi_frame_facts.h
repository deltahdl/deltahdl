#pragma once

namespace delta {

struct VpiObject;

struct VpiFrameFacts {
  VpiObject* origin = nullptr;
  VpiObject* stmt = nullptr;
};

}  // namespace delta
