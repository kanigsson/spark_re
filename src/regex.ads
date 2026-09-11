pragma SPARK_Mode (On);
with Spark_Re;
--  Default budget: 512 syntax nodes and 4096 NFA states.

package Regex is new Spark_Re;
