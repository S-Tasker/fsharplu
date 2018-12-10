namespace Microsoft.FSharpLu.Json

open Newtonsoft.Json
open Newtonsoft.Json.Serialization
open Microsoft.FSharp.Reflection
open System.Reflection
open System.Collections.Concurrent
open System

module private EPGConverterHelpers =
    let inline stringEq (a:string) (b:string) =
        a.Equals(b, System.StringComparison.OrdinalIgnoreCase)

    let inline isOptionType (t:System.Type) =
       t.GetTypeInfo().IsGenericType && t.GetGenericTypeDefinition() = typedefof<option<_>>

    let inline isTupleType (t:System.Type) =
       FSharpType.IsTuple t

    let inline isTupleItemProperty (prop:System.Reflection.PropertyInfo) =
        // Item1, Item2, etc. excluding Items[n] indexer. Valid only on tuple types.
        (prop.Name.StartsWith("Item") || prop.Name = "Rest") && (Seq.isEmpty <| prop.GetIndexParameters())

module EPGMemorised = 
    let inline memorise (f: 'key -> 'result) =
        let d = ConcurrentDictionary<'key, 'result>()
        fun key -> d.GetOrAdd(key, f)

    let getUnionCaseFields = memorise FSharpValue.PreComputeUnionReader
    let getUnionTag = memorise FSharpValue.PreComputeUnionTagReader
    let getUnionCasesByTag = memorise (fun t -> FSharpType.GetUnionCases(t) |> Array.map (fun x -> x.Tag, x) |> dict)

    let getUnionCasesMemorised = memorise FSharpType.GetUnionCases

    let constructUnionCase = memorise FSharpValue.PreComputeUnionConstructor

    let getUnionCaseProperyInfoFields = memorise (fun (case: UnionCaseInfo) -> case.GetFields())

    let findNoFieldsMatchingUnionCaseByNameAndType  = 
        memorise <| fun (objectType, caseName) -> 
            let cases = getUnionCasesMemorised objectType
            cases |> Array.tryFind (fun case -> EPGConverterHelpers.stringEq case.Name caseName && (getUnionCaseProperyInfoFields case |> Array.isEmpty))

    let findMatchingUnionCaseByNameAndType  = 
        memorise <| fun (objectType, caseName) -> 
            let cases = getUnionCasesMemorised objectType
            cases |> Array.tryFind (fun case -> EPGConverterHelpers.stringEq case.Name caseName)

    let getUnionTagOfValue v =
        let t = v.GetType()
        getUnionTag t v

    let inline getUnionFields v =
        let cases = getUnionCasesByTag (v.GetType())
        let tag = getUnionTagOfValue v
        let case = cases.[tag]
        let unionReader = getUnionCaseFields case
        (case, unionReader v)

    let SomeFieldIdentifier = "Some"

    /// Determine if a given type has a field named 'Some' which would cause
    /// ambiguity if nested under an option type without being boxed
    let hasFieldNamedSome =
        memorise
            (fun (t:System.Type) ->
                EPGConverterHelpers.isOptionType t // the option type itself has a 'Some' field
                || (FSharpType.IsRecord t && FSharpType.GetRecordFields t |> Seq.exists (fun r -> EPGConverterHelpers.stringEq r.Name SomeFieldIdentifier))
                || (FSharpType.IsUnion t && FSharpType.GetUnionCases t |> Seq.exists (fun r -> EPGConverterHelpers.stringEq r.Name SomeFieldIdentifier)))

open EPGConverterHelpers
open EPGMemorised

/// Serializers for F# discriminated unions improving upon the stock implementation by JSon.Net
/// The default formatting used by Json.Net to serialize F# discriminated unions
/// and Option types is too verbose. This module implements a more succinct serialization
/// for those data types.
/// This module also removes the property name from the resulting object of the Discriminated Union.
type EPGCompactUnionJsonConverter(?tupleAsHeterogeneousArray:bool) =
    inherit Newtonsoft.Json.JsonConverter()

    ///  By default tuples are serialized as heterogeneous arrays.
    let tupleAsHeterogeneousArray = defaultArg tupleAsHeterogeneousArray true
    let canConvertMemorised =
        memorise
            (fun objectType ->
                (   // Include F# discriminated unions
                    FSharpType.IsUnion objectType
                    // and exclude the standard FSharp lists (which are implemented as discriminated unions)
                    && not (objectType.GetTypeInfo().IsGenericType && objectType.GetGenericTypeDefinition() = typedefof<_ list>)
                )
                // include tuples
                || tupleAsHeterogeneousArray && FSharpType.IsTuple objectType
            )

    override __.CanConvert(objectType:System.Type) = canConvertMemorised objectType

    override __.WriteJson(writer:JsonWriter, value:obj, serializer:JsonSerializer) =
        let t = value.GetType()

        let convertName =
            match serializer.ContractResolver with
            | :? DefaultContractResolver as resolver -> resolver.GetResolvedPropertyName
            | _ -> id

        // Option type?
        if isOptionType t then
            let cases = getUnionCasesMemorised t
            let none, some = cases.[0], cases.[1]

            let case, fields = getUnionFields value

            if case = none then
                () // None is serialized as just null

            // Some _
            else
                // Handle cases `Some None` and `Some null`
                let innerType = (getUnionCaseProperyInfoFields some).[0].PropertyType
                let innerValue = fields.[0]
                if isNull innerValue then
                    writer.WriteStartObject()
                    writer.WritePropertyName(convertName SomeFieldIdentifier)
                    writer.WriteNull()
                    writer.WriteEndObject()
                // Some v with v <> null && v <> None
                else
                    // Is it nesting another option: `(e.g., "Some (Some ... Some ( ... )))"`
                    // or any other type with a field named 'Some'?
                    if hasFieldNamedSome innerType then
                        // Preserved the nested structure through boxing
                        writer.WriteStartObject()
                        writer.WritePropertyName(convertName SomeFieldIdentifier)
                        serializer.Serialize(writer, innerValue)
                        writer.WriteEndObject()
                    else
                        // Type is option<'a> where 'a does not have a field named 'Some
                        // (and therfore in particular is NOT an option type itself)
                        // => we can simplify the Json by omitting the `Some` boxing
                        // and serializing the nested object directly
                        serializer.Serialize(writer, innerValue)
        // Tuple
        else if tupleAsHeterogeneousArray && isTupleType t then
            let v = FSharpValue.GetTupleFields value
            serializer.Serialize(writer, v)
        // Discriminated union
        else
            let case, fields = getUnionFields value

            match fields with
            // Field-less union case
            | [||] -> writer.WriteValue(convertName case.Name)
            // Case with single field
            | [|onefield|] ->
                serializer.Serialize(writer, onefield)
            // Case with list of fields
            | _ ->
                serializer.Serialize(writer, fields)

    override __.ReadJson(reader:JsonReader, objectType:System.Type, existingValue:obj, serializer:JsonSerializer) =
        failwithf "ReadJson is not Implemented"

/// Compact serializer
module EPGCompact =
    open System.Runtime.CompilerServices

    /// Create Json.Net serialization settings with specified converter
    let createJsonNetSettings (c:JsonConverter) =
        let s =
            JsonSerializerSettings(
                NullValueHandling = NullValueHandling.Ignore,

                // Strict deserialization (MissingMemberHandling) is not technically needed for
                // compact serialization but because it avoids certain ambiguities it guarantees
                // that the deserialization coincides with the default Json deserialization
                // ('coincides' meaning 'if the deserialization succeeds they both return the same object')
                // Subsequently this allows us to very easily define the BackwardCompatible serializer which
                // deserializes Json in both Compact and Default format.
                MissingMemberHandling = MissingMemberHandling.Error
        )
        s.Converters.Add(c)
        s

    module Settings =
        /// Compact serialization where tuples are serialized as JSON objects
        type TupleAsObjectSettings =
            static member settings = createJsonNetSettings <| EPGCompactUnionJsonConverter(false)
            static member formatting = Formatting.Indented

        /// Compact serialization where tuples are serialized as heterogeneous arrays
        type TupleAsArraySettings =
            static member settings = createJsonNetSettings <| EPGCompactUnionJsonConverter(true)
            static member formatting = Formatting.Indented


    type private S = With<Settings.TupleAsArraySettings>

    /// Serialize an object to Json with the specified converter
    [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
    let inline serialize< ^T> x = S.serialize x
    /// Serialize an object to Json with the specified converter and save the result to a file
    [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
    let inline serializeToFile< ^T> file obj = S.serializeToFile file obj
    /// Try to deserialize json to an object of type ^T
    [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
    let inline tryDeserialize< ^T> json = S.tryDeserialize< ^T> json
    /// Try to read Json from a file and desrialized it to an object of type ^T
    [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
    let inline tryDeserializeFile< ^T> file = S.tryDeserializeFile< ^T> file
    /// Try to deserialize a stream to an object of type ^T
    [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
    let inline tryDeserializeStream< ^T> stream = S.tryDeserializeStream< ^T> stream
    /// Deserialize a Json to an object of type ^T
    [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
    let inline deserialize< ^T> json : ^T = S.deserialize< ^T> json
    /// Read Json from a file and desrialized it to an object of type ^T
    [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
    let inline deserializeFile< ^T> file = S.deserializeFile< ^T> file
    /// Deserialize a stream to an object of type ^T
    [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
    let inline deserializeStream< ^T> stream = S.deserializeStream< ^T> stream

    /// Legacy compact serialization where tuples are serialized as objects instead of arrays
    module Legacy =
        type private S = With<Settings.TupleAsObjectSettings>

        /// Serialize an object to Json with the specified converter
        [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
        let inline serialize< ^T> x = S.serialize x
        /// Serialize an object to Json with the specified converter and save the result to a file
        [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
        let inline serializeToFile< ^T> file obj = S.serializeToFile file obj
        /// Try to deserialize json to an object of type ^T
        [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
        let inline tryDeserialize< ^T> json = S.tryDeserialize< ^T> json
        /// Try to read Json from a file and desrialized it to an object of type ^T
        [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
        let inline tryDeserializeFile< ^T> file = S.tryDeserializeFile< ^T> file
        /// Try to deserialize a stream to an object of type ^T
        [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
        let inline tryDeserializeStream< ^T> stream = S.tryDeserializeStream< ^T> stream
        /// Deserialize a Json to an object of type ^T
        [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
        let inline deserialize< ^T> json : ^T = S.deserialize< ^T> json
        /// Read Json from a file and desrialized it to an object of type ^T
        [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
        let inline deserializeFile< ^T> file = S.deserializeFile< ^T> file
        /// Deserialize a stream to an object of type ^T
        [<MethodImplAttribute(MethodImplOptions.NoInlining)>]
        let inline deserializeStream< ^T> stream = S.deserializeStream< ^T> stream
