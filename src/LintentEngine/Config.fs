(*
 * TypeDroid - LintentEngine
 * Prelude.fs: misc
 * (C) 2012 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
#light

module LintentEngine.Config

open System
open FSharpCommon.Prelude

module Comm =
    let fatal = "[FATAL]"
    let hint_tag = "[HINT]"
    let issue_tag = "[ISSUE]"
    let lintent_ip_address = "127.0.0.1"
    let lintent_port = 52341
    let separator = "$&$"

module Log =
    open FSharpCommon.Log

    let cfg =
        let l = new FSharpCommon.Log.config ()
        l.show_priority <- false
        l.show_datetime <- false
        l.show_urgency <- false
        #if DEBUG
        #else
        l.debug_threshold <- Unmaskerable
        l.msg_threshold <- Normal
        l.warn_threshold <- Min
        l.hint_threshold <- Min
        #endif
        l

    let verbose_pretty_location = false


module X =
    let api_calls_filename = """permissionmap\APICalls.txt"""
    let implicit_calls_filename = """permissionmap\startingActivities.txt"""
    let service_calls_filename = """permissionmap\startingServices.txt"""

module Lint =

    let android_sdk_paths =
      [
        """%ANDROID_SDK%"""
        """%ProgramFiles%\Android\android-sdk"""
        """%ProgramFiles(x86)%\Android\android-sdk"""
        """%USERPROFILE%\android-sdks"""
      ] |> List.map Environment.ExpandEnvironmentVariables

    let exe_relative_filename = """tools\lint.bat"""

    let jars_path = sprintf """C:\Users\%s\.android\lint""" Environment.UserName

    module Lintent =
        let args_relative_filename = "lintent_args.txt"

        let client_mode_args_file_content = "--client-mode"
   
module Parsing =

    let detailed_error_context = false

module Typing =
    
    let fallback_intent_extra_key i e = sprintf "__intent_extra_key__%s_%d" i (e.GetHashCode ())

    let fallback_intent_action_string e = sprintf "__intent_action_string__%d" (e.GetHashCode ())

    let fallback_startActivityForResult_code _ e = e.GetHashCode ()

    let pending_intent_default_key = "__pending_intent_default_key"

    let mutable perform_component_typing = true

    let mutable perform_dlm_typing = true

    let mutable perform_perms_typing = true

module Dlm =

    let pretty_bottom = "_"
    let pretty_top = "^"

    let label_annotation = ["DlmLabel"; "Label"; "L"]
    let principal_annotation = ["DlmPrincipal"; "Principals"; "P"]
    let declassify_annotation = ["DlmDeclassify"; "Declassify"]
    let endorse_annotation = ["DlmEndorse"; "Endorse"]
    let begin_annotation = ["DlmBeginLabel"; "DlmBegin"; "BeginLabel"; "Begin"; "B"]
    let return_annotation = ["DlmReturnLabel"; "DlmReturn"; "ReturnLabel"; "Return"; "R"]
    let authority_annotation = ["DlmAuthorityLabel"; "DlmAuthority"; "AuthorityLabel"; "Authority"; "A"]


module Java =

    module Annot =
        let intent = ["LIntent"; "Intent"]

        module Priv =
            let annotation = ["priv"; "Priv"]
            let endorse = "endorse"
            let declassify = "declassify"

    module Names =

        let private lang s = sprintf "java.lang.%s" s

        module Type =

            let Null = "javax.lang.model.type.NullType"
            let Class = lang "Class"
            let Object = lang "Object"
            let String = lang "String"
            let Array = lang "Array"
            let Integer = lang "Integer"
            let Float = lang "Float"
            let Double = lang "Double"
            let Short = lang "Short"
            let Long = lang "Long"
            let Char = lang "Char"
            let Boolean = lang "Boolean"
            let Byte = lang "Byte"
            let CharSequence = lang "CharSequence"
            let ArrayList = "java.util.ArrayList"
            let Serializable = "java.io.Serializable"

            let private android ns s = sprintf "android.%s.%s" ns s
            
            let Context = android "content" "Context"
            let ContextWrapper = android "content" "ContextWrapper"
            let ContextThemeWrapper = android "view" "ContextThemeWrapper"
            let Activity = android "app" "Activity"
            let AccountAuthenticatorActivity = android "app" "AccountAuthenticatorActivity"
            let ActivityGroup = android "app" "ActivityGroup"
            let AliasActivity = android "app" "AliasActivity"
            let BasicDream = android "app" "BasicDream"
            let ExpandableListActivity = android "app" "ExpandableListActivity"
            let FragmentActivity = android "app" "FragmentActivity"
            let ListActivity = android "app" "ListActivity"
            let NativeActivity = android "app" "NativeActivity"   
            let Service = android "app" "Service"
            let AbstractInputMethodService = android "app" "AbstractInputMethodService"
            let AccessibilityService = android "app" "AccessibilityService"
            let IntentService = android "app" "IntentService"
            let RecognitionService = android "app" "RecognitionService"
            let RemoteViewsService = android "app" "RemoteViewsService"
            let SpellCheckerService = android "app" "SpellCheckerService"
            let TextToSpeechService = android "app" "TextToSpeechService"
            let VpnService = android "app" "VpnService"
            let WallpaperManager = android "app" "WallpaperManager"
            let WallpaperService = android "app" "WallpaperService"

            let Intent = android "content" "Intent"
            let PendingIntent = android "app" "PendingIntent"
            let Bundle = android "os" "Bundle"
            let Vibrator = android "os" "Vibrator"
            let Location = android "location" "Location"
            let LocationManager = android "location" "LocationManager"
            let LocationProvider = android "location" "LocationProvider"
            let MenuInflater = android "view" "MenuInflater"
            let Menu = android "view" "Menu"
            let Camera = android "hardware" "Camera"

        module Method =

            module Intent =
                let putExtra = "putExtra"
                let getExtra = "get(\w+)Extra"

            module Activity =
                let setResult = "setResult"
                let startActivityForResult = "startActivityForResult"
                let startActivity = "startActivity"
                let startService = "startService"
                let startActivities = "startActivities"
                let onCreate = "onCreate"
                let onActivityResult = "onActivityResult"
                let getIntent = "getIntent"

            module PendingIntent =
                let getActivities = "getActivities"
                let getActivity = "getActivity"


    module T = Names.Type
    let implicit_imports =
      [
        T.Class
        T.Object
        T.String
        T.Array
        T.Integer
        T.Float
        T.Double
        T.Short
        T.Long
        T.Char
        T.Boolean
        T.Byte
        T.CharSequence
        T.ArrayList
      ]

