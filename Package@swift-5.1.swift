// swift-tools-version:5.1

import PackageDescription

let package = Package(
    name: "ForEachField",
    products: [
        .library(name: "ForEachField", targets: ["ForEachField"]),
    ],
    targets: [
        .target(name: "CForEachFieldSwiftRuntimeHelpers"),
        .target(name: "ForEachField", dependencies: ["CForEachFieldSwiftRuntimeHelpers"]),
        .testTarget(name: "ForEachFieldTests", dependencies: ["ForEachField"]),
    ],
    cxxLanguageStandard: .cxx14
)
