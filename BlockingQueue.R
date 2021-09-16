library(ggplot2)
library(dplyr)
library(plotly)

data <- read.csv(header=TRUE, sep = "#", file = "output.csv") #file.choose())

summary = summarise(group_by(data,P,C,B,F,Level),
  # sd_WaitSet = sd(WaitSet),
  # sd_EP = sd(EP),
  # sd_EC = sd(EC),
  # sd_Lock = sd(lock),
  # sd_Worked = sd(worked),
  #WaitSet = mean(WaitSet),
  #EP = mean(EP),
  #EC = mean(EC),
  lock = mean(lock),
  worked = mean(worked)
)

configs <- distinct(summary[1:3])

plts <- list()

for (conf in 1:nrow(configs)) {
  p <- configs[conf,"P"]
  c <- configs[conf,"C"]
  b <- configs[conf,"B"]
  df <- filter(summary, P==p, C==c, B==b)
  ## Locks
  p1 <- plot_ly(df, y = ~lock, x = ~Level, color = ~F, type = 'scatter', mode = 'markers') %>%
    add_markers() %>% layout(yaxis=list(title=paste(p,c,b)))
  ## Throughput
  p2 <- plot_ly(df, y = ~worked, x = ~Level, color=~F, type = 'scatter', mode = 'lines') %>%
    add_markers()
  
#  plts <- append(plts, list(subplot(p1, p2, shareY = TRUE)))
  plts <- append(plts, list(p2))
}

subplot(plts, nrows = 4, titleX = TRUE, titleY = TRUE)
