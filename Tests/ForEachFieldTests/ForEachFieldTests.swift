import CoreFoundation
import Foundation
import XCTest
import ForEachField

private struct TestStruct {
    var int = 0
    var double = 0.0
    var bool = false
}

private struct GenericStruct<T> {
    var int = 0
    var first: T
    var second: T
}

private enum TestEnum {
    case one
    case two
    case three(TestStruct)
}

private class BaseClass {
    var superInt = 0
    init() {}
}

private class TestClass: BaseClass {
    var int = 0
    var double = 0.0
    var bool = false
    override init() {}
}

private class TestSubclass: TestClass {
    var strings: [String] = []
    override init() {}
}

private class GenericClass<T, U>: BaseClass {
    var first: T
    var second: U

    init(_ t: T, _ u: U) {
        self.first = t
        self.second = u
    }
}

private class GenericSubclass<V, W>: GenericClass<V, Bool> {
    var third: W

    init(_ v: V, _ w: W) {
        self.third = w
        super.init(v, false)
    }
}

private class OwnershipTestClass: BaseClass {
    weak var test1: TestClass?
    unowned var test2: TestClass
    unowned(unsafe) var test3: TestClass

    init(_ t: TestClass) {
        self.test1 = t
        self.test2 = t
        self.test3 = t
    }
}

private struct SimilarToNSPoint {
    var x: Double
    var y: Double
}

private struct SimilarToNSSize {
    var width: Double
    var height: Double
}

private struct SimilarToNSRect {
    var origin: SimilarToNSPoint
    var size: SimilarToNSSize
}

private struct ContainsObject {
    var obj: TestClass
}

private struct ContainsForeignObject {
    var cfObject: CFMutableArray
}

class NSObjectSubclass: NSObject {
    var point: (Double, Double)

    init(x: Double, y: Double) {
        self.point = (x, y)
    }
}

class EmptyNSObject: NSObject {}

class TestJSONEncoder: JSONEncoder {
    var int: Int = 0
    var bool: Bool = false
}

class GenericJSONEncoder<T>: JSONEncoder {
    var first: T
    var second: T

    init(first: T, second: T) {
        self.first = first
        self.second = second
    }
}

private typealias ExpectedFields = [(String, Int, Any.Type?, MetadataKind)]

private func checkFields<T>(
    of type: T.Type,
    options: EachFieldOptions = [],
    expectedFields: ExpectedFields
) {

    var actualFields = [(String, Int, Any.Type, MetadataKind)]()
    forEachField(of: T.self, options: options) { charPtr, offset, type, kind in
        actualFields.append((String(cString: charPtr), offset, type, kind))
        return true
    }

    if actualFields.count != expectedFields.count {
        XCTFail("\(actualFields) is not equal to \(expectedFields)")
        return
    }

    let equal = zip(actualFields, expectedFields).allSatisfy { actual, expected in
        var typesEqual = true
        if let expectedType = expected.2 {
            typesEqual = expectedType == actual.2
        }
        return actual.0 == expected.0 &&
               actual.1 == expected.1 &&
               typesEqual &&
               actual.3 == expected.3
    }

    XCTAssert(equal, "\(actualFields) is not equal to \(expectedFields)")
}

private protocol ExistentialProtocol {}

extension TestStruct: ExistentialProtocol {}
extension GenericStruct: ExistentialProtocol {}
extension GenericSubclass: ExistentialProtocol {}

extension ExistentialProtocol {
    fileprivate static func doCheckFields(
        options: EachFieldOptions = [],
        expectedFields: ExpectedFields
    ) {
        checkFields(of: Self.self, options: options, expectedFields: expectedFields)
    }
}

private func checkFieldsAsExistential(
    of type: ExistentialProtocol.Type,
    options: EachFieldOptions = [],
    expectedFields: ExpectedFields
) {
    type.doCheckFields(options: options, expectedFields: expectedFields)
}

private func _withTypeEncodingCallback(encoding: inout String,
                                       name: UnsafePointer<CChar>,
                                       offset: Int,
                                       type: Any.Type,
                                       kind: MetadataKind) -> Bool {
    if type == Bool.self {
        encoding += "B"
        return true
    } else if type == Int.self {
        if MemoryLayout<Int>.size == MemoryLayout<Int64>.size {
            encoding += "q"
        } else if MemoryLayout<Int>.size == MemoryLayout<Int32>.size {
            encoding += "l"
        } else {
            return false
        }
        return true
    } else if type == Double.self {
        encoding += "d"
        return true
    }

    switch kind {
    case .struct:
        encoding += "{"
        defer { encoding += "}" }
        forEachField(of: type) { name, offset, type, kind in
            _withTypeEncodingCallback(encoding: &encoding,
                                      name: name,
                                      offset: offset,
                                      type: type,
                                      kind: kind)
        }
    case .class:
        encoding += "@"
    default:
        break
    }
    return true
}

private func getTypeEncoding<T>(_ type: T.Type) -> String? {
    var encoding = ""
    forEachField(of: type) { name, offset, type, kind in
        _withTypeEncodingCallback(encoding: &encoding,
                                  name: name,
                                  offset: offset,
                                  type: type,
                                  kind: kind)
    }
    return "{\(encoding)}"
}

private let classOffset = MemoryLayout<Int>.stride * 2

private var jsonEncoderFields: (fields: ExpectedFields, nextFieldOffset: Int) {
    let outputFormattingOffset = classOffset
    let dateEncodingStrategyOffset = outputFormattingOffset +
        MemoryLayout<JSONEncoder.OutputFormatting>.stride
    let dataEncodingStrategyOffset = dateEncodingStrategyOffset +
        MemoryLayout<JSONEncoder.DateEncodingStrategy>.stride
    let nonConformingFloatEncodingStrategyOffset = dataEncodingStrategyOffset +
        MemoryLayout<JSONEncoder.DataEncodingStrategy>.stride
    let keyEncodingStrategyOffset = nonConformingFloatEncodingStrategyOffset +
        MemoryLayout<JSONEncoder.NonConformingFloatEncodingStrategy>.stride
    let userInfoOffset = keyEncodingStrategyOffset +
        MemoryLayout<JSONEncoder.KeyEncodingStrategy>.stride
    let fields: ExpectedFields = [
        ("outputFormatting",
         outputFormattingOffset,
         JSONEncoder.OutputFormatting.self,
         .struct),
        ("dateEncodingStrategy",
         dateEncodingStrategyOffset,
         JSONEncoder.DateEncodingStrategy.self,
         .enum),
        ("dataEncodingStrategy",
         dataEncodingStrategyOffset,
         JSONEncoder.DataEncodingStrategy.self,
         .enum),
        ("nonConformingFloatEncodingStrategy",
         nonConformingFloatEncodingStrategyOffset,
         JSONEncoder.NonConformingFloatEncodingStrategy.self,
         .enum),
        ("keyEncodingStrategy",
         keyEncodingStrategyOffset,
         JSONEncoder.KeyEncodingStrategy.self,
         .enum),
        ("userInfo",
         userInfoOffset,
         [CodingUserInfoKey : Any].self,
         .struct)
    ]
    return (fields: fields,
            nextFieldOffset: userInfoOffset +
                MemoryLayout<[CodingUserInfoKey : Any]>.stride)
}

final class ForEachFieldTests: XCTestCase {
    static let allTests = [
        ("testTuple", testTuple),
        ("testEnum", testEnum),
        ("testStruct", testStruct),
        ("testBuiltinTypes", testBuiltinTypes),
        ("testAnyObject", testAnyObject),
        ("testAny", testAny),
        ("testGenericStruct", testGenericStruct),
        ("testClass", testClass),
        ("testOwnershipTestClass", testOwnershipTestClass),
        ("testNSObjectSubclass", testNSObjectSubclass),
        ("testWithTypeEncoding", testWithTypeEncoding),
    ]

    func testTuple() {
        checkFields(
            of: (Int, Bool).self,
            expectedFields: [
                (".0", 0,                        Int.self,  .struct),
                (".1", MemoryLayout<Int>.stride, Bool.self, .struct)
            ]
        )

        checkFields(
            of: (a: Int, b: Bool).self,
            expectedFields: [
                ("a", 0,                        Int.self,  .struct),
                ("b", MemoryLayout<Int>.stride, Bool.self, .struct)
            ]
        )
    }

    func testEnum() {
        checkFields(of: TestEnum.self, expectedFields: [])
    }

    func testStruct() {
        checkFields(
            of: TestStruct.self,
            expectedFields: [
                ("int", 0, Int.self, .struct),
                ("double", MemoryLayout<Double>.stride, Double.self, .struct),
                ("bool", MemoryLayout<Double>.stride * 2, Bool.self, .struct),
            ]
        )

        checkFieldsAsExistential(
            of: TestStruct.self,
            expectedFields: [
                ("int", 0, Int.self, .struct),
                ("double", MemoryLayout<Double>.stride, Double.self, .struct),
                ("bool", MemoryLayout<Double>.stride * 2, Bool.self, .struct),
            ]
        )

        // Applying to struct type with .classType option fails
        XCTAssertFalse(
            forEachField(of: TestStruct.self, options: .classType) { _, _, _, _ in true }
        )
    }

    func testBuiltinTypes() {
        checkFields(
            of: Int.self,
            expectedFields: [
                ("_value", 0, nil, .opaque)
            ]
        )
    }

    func testAnyObject() {
        // TODO
//        checkFields(of: AnyObject.self, expectedFields: [])
    }

    func testAny() {
        // TODO
//        checkFields(of: Any.self, expectedFields: [])
    }

    func testMetatype() {
        checkFields(of: Any.Type.self, expectedFields: [])
    }

    private func checkGenericStruct<T>(_: T.Type, genericTypeKind: MetadataKind) {
        let firstOffset = max(MemoryLayout<Int>.stride, MemoryLayout<T>.alignment)

        checkFields(
            of: GenericStruct<T>.self,
            expectedFields: [
                ("int", 0, Int.self, .struct),
                ("first", firstOffset, T.self, genericTypeKind),
                ("second", firstOffset + MemoryLayout<T>.stride, T.self, genericTypeKind),
            ]
        )

        checkFieldsAsExistential(
            of: GenericStruct<T>.self,
            expectedFields: [
                ("int", 0, Int.self, .struct),
                ("first", firstOffset, T.self, genericTypeKind),
                ("second", firstOffset + MemoryLayout<T>.stride, T.self, genericTypeKind),
            ]
        )
    }

    func testGenericStruct() {
        checkGenericStruct(Bool.self,
                           genericTypeKind: .struct)
        checkGenericStruct(TestStruct.self,
                           genericTypeKind: .struct)
        checkGenericStruct((TestStruct, TestClass, Int, Int).self,
                           genericTypeKind: .tuple)
    }

    func testClass() {
        let classOffset = MemoryLayout<Int>.stride * 2
        let doubleOffset = classOffset
            + max(MemoryLayout<Int>.stride * 2, MemoryLayout<Double>.stride)

        checkFields(
            of: TestClass.self, options: .classType,
            expectedFields: [
                ("superInt", classOffset, Int.self, .struct),
                ("int", classOffset + MemoryLayout<Int>.stride, Int.self, .struct),
                ("double", doubleOffset, Double.self, .struct),
                ("bool", doubleOffset + MemoryLayout<Double>.stride, Bool.self, .struct),
            ]
        )

        checkFields(
            of: TestSubclass.self, options: .classType,
            expectedFields: [
                ("superInt", classOffset, Int.self, .struct),
                ("int", classOffset + MemoryLayout<Int>.stride, Int.self, .struct),
                ("double", doubleOffset, Double.self, .struct),
                ("bool", doubleOffset + MemoryLayout<Double>.stride, Bool.self, .struct),
                ("strings",
                 doubleOffset +
                    MemoryLayout<Double>.stride +
                    MemoryLayout<Array<String>>.stride,
                 Array<String>.self,
                 .struct),
            ]
        )

        let firstOffset = classOffset
            + max(MemoryLayout<Int>.stride, MemoryLayout<TestStruct>.alignment)
        checkFields(
            of: GenericSubclass<TestStruct, TestStruct>.self,
            options: .classType,
            expectedFields: [
                ("superInt", classOffset, Int.self, .struct),
                ("first", firstOffset, TestStruct.self, .struct),
                ("second",
                 firstOffset + MemoryLayout<TestStruct>.size,
                 Bool.self,
                 .struct),
                ("third",
                 firstOffset + MemoryLayout<TestStruct>.stride,
                 TestStruct.self,
                 .struct),
            ]
        )

        checkFields(
            of: GenericSubclass<Int, Never>.self, options: .classType,
            expectedFields: [
                ("superInt", classOffset, Int.self, .struct),
                ("first", classOffset + MemoryLayout<Int>.stride, Int.self, .struct),
                ("second",
                 classOffset + MemoryLayout<Int>.stride * 2,
                 Bool.self,
                 .struct),
                ("third", 0, Never.self, .enum),
            ]
        )

        checkFieldsAsExistential(
            of: GenericSubclass<TestStruct, TestStruct>.self, options: .classType,
            expectedFields: [
                ("superInt", classOffset, Int.self, .struct),
                ("first", firstOffset, TestStruct.self, .struct),
                ("second",
                 firstOffset + MemoryLayout<TestStruct>.size,
                 Bool.self,
                 .struct),
                ("third",
                 firstOffset + MemoryLayout<TestStruct>.stride,
                 TestStruct.self,
                 .struct),
            ]
        )

        // Applying to class type without .classType option fails
        XCTAssertFalse(forEachField(of: TestClass.self) { _, _, _, _ in true })
    }

    func testOwnershipTestClass() {
        checkFields(
            of: OwnershipTestClass.self, options: .classType,
            expectedFields: [
                ("superInt", classOffset, Int.self, .struct),
                ("test1",
                 classOffset + MemoryLayout<Int>.stride,
                 Optional<TestClass>.self,
                 .optional),
                ("test2",
                 classOffset + MemoryLayout<Int>.stride * 2,
                 TestClass.self,
                 .class),
                ("test3",
                 classOffset + MemoryLayout<Int>.stride * 3,
                 TestClass.self,
                 .class),
            ]
        )
    }

    func testNSObjectSubclass() {
        XCTAssertTrue(
            forEachField(of: NSObjectSubclass.self,
                         options: .classType) { charPtr, _, type, _ in
                let fieldName = String(cString: charPtr)
                return type == (Double, Double).self && fieldName == "point"
            }
        )

        XCTAssertTrue(
            forEachField(of: EmptyNSObject.self, options: .classType) { _, _, _, _ in
                true
            }
        )
    }

    func testForeignClass() {
        XCTAssertTrue(
            forEachField(of: CFMutableArray.self, options: .classType) { _, _, _, _ in
                true
            }
        )
    }

    func testResilientClass() {
        checkFields(
            of: JSONEncoder.self,
            options: .classType,
            expectedFields: jsonEncoderFields.0
        )
    }

    func testSubclassOfResilientClass() {
        var (expectedFields, intOffset) = jsonEncoderFields
        expectedFields += [
            ("int", intOffset, Int.self, .struct),
            ("bool", intOffset + MemoryLayout<Int>.stride, Bool.self, .struct)
        ]
        checkFields(
            of: TestJSONEncoder.self,
            options: .classType,
            expectedFields: expectedFields
        )
    }

    func testGenericSubclassOfResilientClass() {
        let (baseClassFields, firstOffset) = jsonEncoderFields

        checkFields(
            of: GenericJSONEncoder<Int>.self,
            options: .classType,
            expectedFields: baseClassFields + [
                ("first", firstOffset, Int.self, .struct),
                ("second", firstOffset + MemoryLayout<Int>.stride, Int.self, .struct)
            ]
        )

        checkFields(
            of: GenericJSONEncoder<JSONEncoder>.self,
            options: .classType,
            expectedFields: baseClassFields + [
                ("first", firstOffset, JSONEncoder.self, .class),
                ("second",
                 firstOffset + MemoryLayout<Int>.stride,
                 JSONEncoder.self,
                 .class)
            ]
        )

        checkFields(
            of: GenericJSONEncoder<(a: Int, b: String)>.self,
            options: .classType,
            expectedFields: baseClassFields + [
                ("first", firstOffset, (a: Int, b: String).self, .tuple),
                ("second",
                 firstOffset + MemoryLayout<(a: Int, b: String)>.stride,
                 (a: Int, b: String).self,
                 .tuple)
            ]
        )
    }

    func testWithTypeEncoding() {
        XCTAssertEqual("{@}", getTypeEncoding(ContainsObject.self))
        XCTAssertEqual("{{dd}{dd}}", getTypeEncoding(SimilarToNSRect.self))

        let testEncoding = getTypeEncoding(TestStruct.self)
        XCTAssertTrue("{qdB}" == testEncoding || "{ldB}" == testEncoding)
    }
}
