set(CPACK_PACKAGE_NAME "c2btor")
set(CPACK_PACKAGE_VENDOR "C2BTOR contributors")
set(CPACK_PACKAGE_CONTACT "https://github.com/westtide/c2btor/issues")
set(CPACK_PACKAGE_DESCRIPTION_SUMMARY "C2BTOR translates C programs to bit-precise BTOR2 models")
set(CPACK_PACKAGE_DESCRIPTION
"C2BTOR translates C through CBMC GotoIR to BTOR2 transition systems,
with object memory, IEEE-754 bit-vector circuits and source-mapped
violation witnesses validated through BtorSim and CPAchecker.")

# Package only the explicitly built product, without rebuilding upstream tools.
set(CMAKE_SKIP_INSTALL_ALL_DEPENDENCY TRUE)
set(CPACK_COMPONENTS_ALL c2btor)
set(CPACK_COMPONENTS_GROUPING ALL_COMPONENTS_IN_ONE)
set(CPACK_ARCHIVE_COMPONENT_INSTALL ON)
set(CPACK_DEB_COMPONENT_INSTALL ON)

set(CPACK_PACKAGE_VERSION_MAJOR ${PROJECT_VERSION_MAJOR})
set(CPACK_PACKAGE_VERSION_MINOR ${PROJECT_VERSION_MINOR})
set(CPACK_PACKAGE_VERSION_PATCH ${PROJECT_VERSION_PATCH})

# This should always be set, just isn鈥檛 by default for awkward backward compatibility reasons
set(CPACK_VERBATIM_VARIABLES YES)

# The WiX package generator expects licenses to end in .txt or .rtf...
file(COPY "${CMAKE_CURRENT_SOURCE_DIR}/LICENSE" DESTINATION "${CMAKE_CURRENT_BINARY_DIR}")
file(RENAME "${CMAKE_CURRENT_BINARY_DIR}/LICENSE" "${CMAKE_CURRENT_BINARY_DIR}/LICENSE.txt")

set(CPACK_RESOURCE_FILE_LICENSE "${CMAKE_CURRENT_BINARY_DIR}/LICENSE.txt")
set(CPACK_PACKAGE_RESOURCE_FILE_README "${CMAKE_CURRENT_SOURCE_DIR}/README.md")

# Automatically find dependencies for shared libraries
set(CPACK_DEBIAN_PACKAGE_SHLIBDEPS YES)

# In addition, we depend on gcc for preprocessing and bash-completion to make
# C2BTOR's bash completion work
set(CPACK_DEBIAN_PACKAGE_DEPENDS "gcc, bash-completion")

# Enable debug output so that we can see the dependencies being generated in the
# logs
set(CPACK_DEBIAN_PACKAGE_DEBUG YES)

# For windows we need to set up product and update GUID
# See: https://docs.microsoft.com/en-us/windows/win32/msi/productcode
# and  https://docs.microsoft.com/en-us/windows/win32/msi/upgradecode
# confusingly, the "product" GUID here is the one that changes between releases,
# the upgrade one is the one that stays the same. CMake takes care of setting these,
# but we want to fix the upgrade GUID to a specific value so new installs override
# old ones.
set(NIL_UUID "00000000-0000-0000-0000-000000000000")
string(UUID CPACK_WIX_UPGRADE_GUID
  NAMESPACE ${NIL_UUID}
  NAME "c2btor"
  TYPE SHA1
  UPPER)


# Keep the install location stable across C2BTOR releases.
set(CPACK_PACKAGE_INSTALL_DIRECTORY "c2btor")


# TODO packages for other platforms
if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  set(CPACK_GENERATOR TGZ DEB)
elseif(WIN32)
  # Note: We don't ship VC redistributables with
  # the windows installer; We assume these are likely
  # already present on a developer machine, and if not
  # can easily be installed separately via vcredist.exe
  set(CPACK_GENERATOR ZIP WIX)
endif()

# Yes, this has to go at the bottom,
# otherwise it can鈥檛 take into account
# all the variables we set above!
include(CPack)
