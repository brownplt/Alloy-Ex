(ns github_analysis.core
  (:use [clojure xml repl])
  (:require [clojure [zip :as zip]]))

(defn get-file [f]
  (zip/xml-zip (parse f)))

#_ (tuples :authentication "StateOfServer$0" "UserName$0" "Password$0")
#_ (StateOfServer$0 :authentication "UserName$0" "Password$0")

#_ {:authentication {["StateOfServer$0" "UserName$0" "Password$0"] "UserAccount$0"
                     ["StateOfServer$1" "UserName$1" "Password$1"] "UserAccount$1"}
    :identification {[blah] blah
                     [blah blah] blah}
    :all {nil {:authentication [[asdf asdf adsf]
                                [asfd adf asdf]]
               :identification [[asfd af asf]
                                [adsf adfa dsf]]}}}

(defn make-tuple-fn [tuple-data]
  (let [processed-tuple-data (assoc (into {}
                                          (for [[tuple-name tuples] tuple-data]
                                            [tuple-name
                                             (apply merge-with #_ #(concat %2 %1) into
                                                    (for [tuple tuples]
                                                      {(vec (butlast tuple))
                                                       #{(last tuple)}}))]))
                               :all {nil tuple-data})]
    (fn [type & args]
      ((processed-tuple-data type) args))))

(defn parse-file [f]
  (let [all-objects (zip/children (zip/down f))
        {:keys [sig field]} (group-by :tag all-objects)]
    {:data (into {}
                 (for [{{label :label} :attrs
                        contents :content} sig]
                   [label (map (comp #(.substring % 5) :label :attrs) contents)]))
     :tuples (make-tuple-fn
              (apply merge-with concat
                     (for [{{label :label} :attrs
                            contents :content} field]
                       {(keyword label)
                        (map (fn [{tuple :content}]
                               (map (comp :label :attrs) tuple))
                             (filter #(= (:tag %) :tuple)
                                     contents))})))}))

(defn object-type [o]
  (second (re-find #"(.*)\$" o)))

(def difficulties
     {["LoggedInMainPage" "MyReposPage"] 1
      ["LoggedInMainPage" "RepoMemberPage"] 8})

(defn difficulty? [p1 p2]
  (difficulties [(object-type p1)
                 (object-type p2)]
                -1))

(def discoverabilities
     #{["LoggedInMainPage" "MyReposPage"]
       ["MyReposPage" "RepoMemberPage"]
       ["MyReposPage" "RepoOwnerPage"]
       })

(defn discoverable? [p1 p2]
  (let [t1 (object-type p1)
        t2 (object-type p2)]
    (not (not
          (case t2
                "LoggedInMainPage" true
                "LoginPage" true
                "CreateRepoPageNN" true #_ (#{"MyReposPage" "LoggedInMainPage"} t1)
                "CreateRepoPageIN" true #_ (#{"CreateRepoPageNN" "CreateRepoPageIN" "CreateRepoPageVN"} t1)
                "CreateRepoPageVN" true #_ (#{"CreateRepoPageNN" "CreateRepoPageIN" "CreateRepoPageVN"} t1)
                "MyReposPage" true
                "RepoMemberPage" (#{"MyReposPage"} t1)
                "RepoOwnerPage" (#{"MyReposPage" "CreateRepoVN"} t1)
                "CollaboratorPage" true #_ (#{"RepoOwnerPage" "CollaboratorPage"} t1)
                false))))
  #_ (not (not
           (discoverabilities [(object-type p1)
                               (object-type p2)]))))
#_ ({:tag :sig,
     :attrs {:label "this/Repo", :ID "4", :parentID "2"},
     :content [{:tag :atom, :attrs {:label "Repo$0"}, :content nil}
               {:tag :atom, :attrs {:label "Repo$1"}, :content nil}
               {:tag :atom, :attrs {:label "Repo$2"}, :content nil}
               {:tag :atom, :attrs {:label "Repo$3"}, :content nil}
               {:tag :atom, :attrs {:label "Repo$4"}, :content nil}]}
    {:tag :sig,
     :attrs {:label "this/StateOfServer", :ID "8", :parentID "2"},
     :content [{:tag :atom, :attrs {:label "StateOfServer$0"}, :content nil}
               {:tag :atom, :attrs {:label "StateOfServer$1"}, :content nil}]}
    
    {:tag :field,
     :attrs {:label "repos", :ID "9", :parentID "8"},
     :content [{:tag :tuple,
                :attrs nil,
                :content [{:tag :atom, :attrs {:label "StateOfServer$0"}, :content nil}
                          {:tag :atom, :attrs {:label "Repo$0"}, :content nil}]}
               {:tag :tuple,
                :attrs nil,
                :content [{:tag :atom, :attrs {:label "StateOfServer$0"}, :content nil}
                          {:tag :atom, :attrs {:label "Repo$1"}, :content nil}]}
               {:tag :tuple,
                :attrs nil,
                :content [{:tag :atom, :attrs {:label "StateOfServer$0"}, :content nil}
                          {:tag :atom, :attrs {:label "Repo$2"}, :content nil}]}
               {:tag :tuple,
                :attrs nil,
                :content [{:tag :atom, :attrs {:label "StateOfServer$0"}, :content nil}
                          {:tag :atom, :attrs {:label "Repo$3"}, :content nil}]}
               {:tag :tuple,
                :attrs nil,
                :content [{:tag :atom, :attrs {:label "StateOfServer$0"}, :content nil}
                          {:tag :atom, :attrs {:label "Repo$4"}, :content nil}]}
               {:tag :tuple,
                :attrs nil,
                :content [{:tag :atom, :attrs {:label "StateOfServer$1"}, :content nil}
                          {:tag :atom, :attrs {:label "Repo$0"}, :content nil}]}
               {:tag :tuple,
                :attrs nil,
                :content [{:tag :atom, :attrs {:label "StateOfServer$1"}, :content nil}
                          {:tag :atom, :attrs {:label "Repo$1"}, :content nil}]}
               {:tag :tuple,
                :attrs nil,
                :content [{:tag :atom, :attrs {:label "StateOfServer$1"}, :content nil}
                          {:tag :atom, :attrs {:label "Repo$2"}, :content nil}]}
               {:tag :tuple,
                :attrs nil,
                :content [{:tag :atom, :attrs {:label "StateOfServer$1"}, :content nil}
                          {:tag :atom, :attrs {:label "Repo$3"}, :content nil}]}
               {:tag :types,
                :attrs nil,
                :content [{:tag :type, :attrs {:ID "8"}, :content nil}
                          {:tag :type, :attrs {:ID "4"}, :content nil}]}]}
    {:tag :field,
     :attrs {:label "Authentication", :ID "16", :parentID "8"},
     :content [{:tag :tuple,
                :attrs nil,
                :content [{:tag :atom, :attrs {:label "StateOfServer$0"}, :content nil}
                          {:tag :atom, :attrs {:label "UserName$1"}, :content nil}
                          {:tag :atom, :attrs {:label "Password$1"}, :content nil}
                          {:tag :atom, :attrs {:label "UserAccount$1"}, :content nil}]}
               {:tag :tuple,
                :attrs nil,
                :content [{:tag :atom, :attrs {:label "StateOfServer$0"}, :content nil}
                          {:tag :atom, :attrs {:label "UserName$2"}, :content nil}
                          {:tag :atom, :attrs {:label "Password$1"}, :content nil}
                          {:tag :atom, :attrs {:label "UserAccount$0"}, :content nil}]}
               {:tag :tuple,
                :attrs nil,
                :content [{:tag :atom, :attrs {:label "StateOfServer$1"}, :content nil}
                          {:tag :atom, :attrs {:label "UserName$1"}, :content nil}
                          {:tag :atom, :attrs {:label "Password$1"}, :content nil}
                          {:tag :atom, :attrs {:label "UserAccount$1"}, :content nil}]}
               {:tag :tuple,
                :attrs nil,
                :content [{:tag :atom, :attrs {:label "StateOfServer$1"}, :content nil}
                          {:tag :atom, :attrs {:label "UserName$2"}, :content nil}
                          {:tag :atom, :attrs {:label "Password$1"}, :content nil}
                          {:tag :atom, :attrs {:label "UserAccount$0"}, :content nil}]}
               {:tag :types,
                :attrs nil,
                :content [{:tag :type, :attrs {:ID "8"}, :content nil}
                          {:tag :type, :attrs {:ID "6"}, :content nil}
                          {:tag :type, :attrs {:ID "7"}, :content nil}
                          {:tag :type, :attrs {:ID "5"}, :content nil}]}]})