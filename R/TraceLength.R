setwd("/home/markus/src/TLA/models/tutorials/BlockingQueueTLA/R")
data <- read.csv(header=TRUE, file = 'TraceLength.csv')

# Rename column headers for readability.
colnames(data)
names(data)[names(data) == "cons_prod"] <- "|Cons U Prod|"
names(data)[names(data) == "prod"] <- "|Prod|"
names(data)[names(data) == "cons"] <- "|Cons|"


##install.packages("scatterplot3d")
#library(scatterplot3d)
#scatterplot3d(
#  data[,1:3], pch = 19, color = "steelblue",
#  grid = TRUE, box = FALSE,
#  mar = c(3, 3, 0.5, 3)        
#)

##install.packages("GGally")
library(GGally)
library(ggplot2)
ggpairs(data)

##install.packages("ggcorrplot")
library("ggcorrplot")
my_data <- data[, c(1,2,3,4,5)]
corr <- round(cor(my_data), 1)
ggcorrplot(corr, p.mat = cor_pmat(my_data),
           hc.order = TRUE, type = "lower",
           color = c("#FC4E07", "white", "#00AFBB"),
           outline.col = "white", lab = TRUE)
