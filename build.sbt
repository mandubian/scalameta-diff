lazy val ScalametaVersion = "2.0.0-RC1"

lazy val semanticdbSettings = List(
  scalaVersion := "2.12.3", // 2.11.11 is also supported.
  addCompilerPlugin("org.scalameta" % "semanticdb-scalac" % ScalametaVersion cross CrossVersion.full),
  scalacOptions ++= Seq(
    "-Yrangepos"
  )
)

// Build a semanticdb for this project.
lazy val analyzeme = project.settings(
  semanticdbSettings
)

// Build a semanticdb for this project.
lazy val recursion = project.settings(
  scalaVersion := "2.12.3",
  // scalaOrganization := "org.typelevel",
  // scalaVersion      := "2.12.3-bin-typelevel-4",
  scalacOptions ++= Seq(
  //   "-Ykind-polymorphism"
    "-Ypartial-unification"
  ),
  // semanticdbSettings,
  // libraryDependencies += "ch.epfl.scala" %% "scalafix-core" % "0.5.2",
  libraryDependencies += "org.scalameta" %% "scalameta" % ScalametaVersion,
  libraryDependencies += "com.slamdata" %% "matryoshka-core" % "0.21.2",
  libraryDependencies += "com.chuusai" %% "shapeless" % "2.3.2",
  addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.4")
).dependsOn(diff)

lazy val diff = project
  .settings(
    scalaVersion := "2.12.3", // 2.11.11 is also supported, regardless of scalaVersion in analyzeme.
    libraryDependencies += "org.scalameta" %% "scalameta" % ScalametaVersion,
    libraryDependencies += "org.scalameta" %% "contrib" % ScalametaVersion,
    libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value % "provided",
    libraryDependencies += "ch.epfl.scala" %% "scalafix-core" % "0.5.2",
    // (optional) we need to pass the classpath/sourcepath to our analyzer, one way to do that is with
    // sbt-buildinfo. For a cli analyzer, it makes sense to read --classpath and --sourcepath.
    buildInfoPackage := "scala.meta",
    buildInfoKeys := Seq[BuildInfoKey](
      "classpath" -> classDirectory.in(analyzeme, Compile).value.getAbsolutePath,
      "sourcepath" -> baseDirectory.in(ThisBuild).value.getAbsolutePath
    ),
    resolvers += Resolver.sonatypeRepo("releases"),
    addCompilerPlugin("org.scalamacros" % "paradise" % "2.1.0" cross CrossVersion.full)
  )
  .enablePlugins(BuildInfoPlugin) // generate BuildInfo object with sourcepath and classpath.
  .dependsOn(analyzeme) // optional, but convenient to trigger compilation of analyzeme on analyzer/run.
