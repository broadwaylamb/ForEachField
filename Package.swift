// swift-tools-version:5.3

import PackageDescription

let package = Package(
    name: "ForEachField",
    products: [
        .library(name: "ForEachField", targets: ["ForEachField"]),
    ],
    targets: [
        .target(name: "CForEachFieldSwiftRuntimeHelpers"),
        .target(name: "ForEachField",
                dependencies: [
                    .target(name: "CForEachFieldSwiftRuntimeHelpers",
                            condition: .when(platforms: [.macOS, .iOS, .watchOS, .tvOS]))
                ]),
        .testTarget(name: "ForEachFieldTests", dependencies: ["ForEachField"]),
    ],
    cxxLanguageStandard: .cxx14
)
