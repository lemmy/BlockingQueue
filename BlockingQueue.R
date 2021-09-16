library(ggplot2)
library(dplyr)
library(plotly)

data <- read.csv(header=TRUE, sep = "#", file = "output.csv") #file.choose())
#data$Procs <- data$P - data$C

summary = summarise(group_by(data,F,Level),
                    # sd_WaitSet = sd(WaitSet),
                    # sd_EP = sd(EP),
                    # sd_EC = sd(EC),
                    # sd_Lock = sd(lock),
                    # sd_Worked = sd(worked),
                    WaitSet = mean(WaitSet),
                    EP = mean(EP),
                    EC = mean(EC),
                    lock = mean(lock),
                    worked = mean(worked)
)

p1 <- plot_ly(summary, y = ~lock, x = ~Level, color = ~F, type = 'scatter', mode = 'markers') %>%
  add_markers()

p2 <- plot_ly(summary, y = ~worked, x = ~Level, color=~F, type = 'scatter', mode = 'lines') %>%
  add_markers()

subplot(p1, p2, shareY = TRUE)
